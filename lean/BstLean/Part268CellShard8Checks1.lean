import BstLean.Part268CellShard8Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12550_20 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41691263808257 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (90815201593 / 4000000000000 : ℝ))
      (E := (cell12550 ⟨20, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41691263808257 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (90815201593 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_21 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (2083699936817 / 2500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270384052851 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨21, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (2083699936817 / 2500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270384052851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_22 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41656745816991 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270388052221 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨22, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41656745816991 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270388052221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_23 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (20819752516851 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (45407840839 / 2000000000000 : ℝ))
      (E := (cell12550 ⟨23, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (20819752516851 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (45407840839 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_24 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41622276370051 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (283799503227 / 12500000000000 : ℝ))
      (E := (cell12550 ⟨24, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41622276370051 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (283799503227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_25 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (416050598097 / 500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (7095000023 / 312500000000 : ℝ))
      (E := (cell12550 ⟨25, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (416050598097 / 500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (7095000023 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_26 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (8317571067279 / 10000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567601012073 / 25000000000000 : ℝ))
      (E := (cell12550 ⟨26, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (8317571067279 / 10000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567601012073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_27 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83141325867931 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270408034897 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨27, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83141325867931 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270408034897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_28 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (10388370646581 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567603007099 / 25000000000000 : ℝ))
      (E := (cell12550 ⟨28, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (10388370646581 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567603007099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_29 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83072628554931 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270416031393 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨29, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83072628554931 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270416031393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_30 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (20759578995733 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (283802505783 / 12500000000000 : ℝ))
      (E := (cell12550 ⟨30, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (20759578995733 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (283802505783 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_31 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83004027424969 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270424016629 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨31, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83004027424969 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270424016629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_32 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82969762849517 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (7095087509 / 312500000000 : ℝ))
      (E := (cell12550 ⟨32, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82969762849517 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (7095087509 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_33 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82935522225217 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270432006701 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨33, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82935522225217 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270432006701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_34 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41450652760433 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270436029551 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨34, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41450652760433 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270436029551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_35 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82867112705421 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270440014047 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨35, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82867112705421 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270440014047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_36 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41416471873999 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135222009881 / 50000000000000 : ℝ))
      (E := (cell12550 ⟨36, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41416471873999 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135222009881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_37 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (20699699654467 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270448047477 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨37, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (20699699654467 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270448047477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_38 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82764677284459 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (283806504883 / 12500000000000 : ℝ))
      (E := (cell12550 ⟨38, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82764677284459 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (283806504883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_39 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41365289858677 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454091210699 / 20000000000000 : ℝ))
      (E := (cell12550 ⟨39, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41365289858677 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454091210699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12551_20 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83382518557189 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (454050287887 / 20000000000000 : ℝ))
      (E := (cell12551 ⟨20, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83382518557189 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (454050287887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_21 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83347988730287 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (454051084903 / 20000000000000 : ℝ))
      (E := (cell12551 ⟨21, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83347988730287 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (454051084903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_22 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83313483208079 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135129727483 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨22, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83313483208079 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135129727483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_23 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83279001957549 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135131738271 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨23, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83279001957549 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135131738271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_24 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41622272472927 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (113513371733 / 5000000000000 : ℝ))
      (E := (cell12551 ⟨24, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41622272472927 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (113513371733 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_25 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (520063200877 / 625000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270271449551 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨25, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (520063200877 / 625000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270271449551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_26 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83175703508439 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270275466187 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨26, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83175703508439 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270275466187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_27 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (8314131901787 / 10000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567569857303 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨27, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (8314131901787 / 10000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567569857303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_28 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83106958636441 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567570864573 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨28, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83106958636441 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567570864573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_29 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (4153631116607 / 5000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567571859789 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨29, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (4153631116607 / 5000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567571859789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_30 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83038310073123 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567572858151 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨30, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83038310073123 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567572858151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_31 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (16600804365541 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270295440781 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨31, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (16600804365541 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270295440781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_32 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41484878782183 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135149732799 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨32, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41484878782183 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135149732799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_33 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (16587103450349 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567575862543 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨33, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (16587103450349 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567575862543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_34 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41450650429321 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270307454483 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨34, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41450650429321 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270307454483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_35 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82867108354013 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270311479763 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨35, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82867108354013 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270311479763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_36 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (3313317588279 / 4000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (283789433547 / 12500000000000 : ℝ))
      (E := (cell12551 ⟨36, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (3313317588279 / 4000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (283789433547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_37 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (206996987217 / 250000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (141894967481 / 6250000000000 : ℝ))
      (E := (cell12551 ⟨37, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (206996987217 / 250000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (141894967481 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_38 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82764673862917 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (283790431949 / 12500000000000 : ℝ))
      (E := (cell12551 ⟨38, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82764673862917 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (283790431949 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_39 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (8273057660491 / 10000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270327455037 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨39, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (8273057660491 / 10000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270327455037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12552_20 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (10422813687443 / 12500000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135061446603 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨20, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (10422813687443 / 12500000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135061446603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_21 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (2604624374673 / 3125000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (227012690869 / 10000000000000 : ℝ))
      (E := (cell12552 ⟨21, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (2604624374673 / 3125000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (227012690869 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_22 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41656737391889 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270130912001 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨22, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41656737391889 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270130912001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_23 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41639496924629 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270134907151 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨23, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41639496924629 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270134907151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_24 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (20811134288283 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135069448959 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨24, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (20811134288283 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135069448959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_25 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41605052331363 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270142946221 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨25, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41605052331363 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270142946221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_26 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (16635139269107 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (18161175509 / 800000000000 : ℝ))
      (E := (cell12552 ⟨26, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (16635139269107 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (18161175509 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_27 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83141312169219 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135075468279 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨27, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83141312169219 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135075468279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_28 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (20776738025401 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (283769367857 / 12500000000000 : ℝ))
      (E := (cell12552 ⟨28, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (20776738025401 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (283769367857 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_29 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83072616110681 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (45403178033 / 2000000000000 : ℝ))
      (E := (cell12552 ⟨29, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83072616110681 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (45403178033 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_30 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41519152082303 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135081466119 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨30, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41519152082303 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135081466119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_31 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83004016231697 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567541729947 / 25000000000000 : ℝ))
      (E := (cell12552 ⟨31, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83004016231697 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567541729947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_32 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (5185609517527 / 6250000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270170924689 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨32, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (5185609517527 / 6250000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270170924689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_33 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (20733878069863 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270174890057 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨33, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (20733878069863 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270174890057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_34 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82901296197557 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270178934461 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨34, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82901296197557 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270178934461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_35 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41433552001853 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567545735493 / 25000000000000 : ℝ))
      (E := (cell12552 ⟨35, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41433552001853 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567545735493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_36 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (16566587133403 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135093456761 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨36, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (16566587133403 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135093456761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_37 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82798791156757 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135095454243 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨37, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82798791156757 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135095454243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_38 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82764670442363 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454038985483 / 20000000000000 : ℝ))
      (E := (cell12552 ⟨38, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82764670442363 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454038985483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_39 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (10341321686677 / 12500000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454039782387 / 20000000000000 : ℝ))
      (E := (cell12552 ⟨39, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (10341321686677 / 12500000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454039782387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12553_20 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83382500443579 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134997229703 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨20, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83382500443579 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134997229703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_21 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41673985625213 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269998447093 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨21, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41673985625213 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269998447093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_22 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (2082836659027 / 2500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135001211663 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨22, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (2082836659027 / 2500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135001211663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_23 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (8327898574253 / 10000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (45400129009 / 2000000000000 : ℝ))
      (E := (cell12553 ⟨23, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (8327898574253 / 10000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (45400129009 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_24 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41622264680967 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135005207797 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨24, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41622264680967 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135005207797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_25 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83210097186619 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (227001443899 / 10000000000000 : ℝ))
      (E := (cell12553 ⟨25, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83210097186619 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (227001443899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_26 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83175689184079 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270018407201 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨26, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83175689184079 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270018407201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_27 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (3325652212879 / 4000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567505610021 / 25000000000000 : ℝ))
      (E := (cell12553 ⟨27, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (3325652212879 / 4000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567505610021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_28 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83106945568137 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270026423639 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨28, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83106945568137 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270026423639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_29 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41536304945277 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270030418877 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨29, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41536304945277 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270030418877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_30 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83038298257383 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (283754303521 / 12500000000000 : ℝ))
      (E := (cell12553 ⟨30, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83038298257383 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (283754303521 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_31 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83004010636943 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135019226827 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨31, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83004010636943 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135019226827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_32 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (16593949399543 / 20000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270042438701 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨32, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (16593949399543 / 20000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270042438701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_33 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41467753654169 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270046443493 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨33, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41467753654169 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270046443493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_34 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82901291537613 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270050410893 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨34, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82901291537613 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270050410893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_35 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82867099654501 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (227005445929 / 10000000000000 : ℝ))
      (E := (cell12553 ⟨35, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82867099654501 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (227005445929 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_36 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82832931628119 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (28375730173 / 1250000000000 : ℝ))
      (E := (cell12553 ⟨36, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82832931628119 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (28375730173 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_37 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82798787427741 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270062451171 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨37, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82798787427741 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270062451171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_38 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82764667022797 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135033227267 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨38, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82764667022797 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135033227267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_39 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (10341321297859 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (17734925189 / 781250000000 : ℝ))
      (E := (cell12553 ⟨39, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (10341321297859 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (17734925189 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12554_20 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83382491389293 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567466490811 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨20, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83382491389293 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567466490811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_21 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (20836990628239 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134934990719 / 50000000000000 : ℝ))
      (E := (cell12554 ⟨21, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (20836990628239 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134934990719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_22 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83313457939983 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269873988943 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨22, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83313457939983 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269873988943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_23 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (16655795527473 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (283734748721 / 12500000000000 : ℝ))
      (E := (cell12554 ⟨23, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (16655795527473 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (283734748721 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_24 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (4162226078613 / 5000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (283735248461 / 12500000000000 : ℝ))
      (E := (cell12554 ⟨24, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (4162226078613 / 5000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (283735248461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_25 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (20802522427999 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (7093393707 / 312500000000 : ℝ))
      (E := (cell12554 ⟨25, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (20802522427999 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (7093393707 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_26 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83175682024069 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269889988727 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨26, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83175682024069 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269889988727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_27 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (4157064923807 / 5000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269893998217 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨27, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (4157064923807 / 5000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269893998217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_28 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83106939036039 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269897959093 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨28, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83106939036039 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269897959093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_29 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (41536301835879 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269901990837 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨29, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (41536301835879 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269901990837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_30 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83038292351453 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134952989447 / 50000000000000 : ℝ))
      (E := (cell12554 ⟨30, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83038292351453 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134952989447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_31 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (20751001260861 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269909983857 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨31, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (20751001260861 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269909983857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_32 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82969741716213 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567478501909 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨32, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82969741716213 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567478501909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_33 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82935502338401 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (453983598669 / 20000000000000 : ℝ))
      (E := (cell12554 ⟨33, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82935502338401 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (453983598669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_34 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82901286878809 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269922000963 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨34, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82901286878809 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269922000963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_35 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (41433547653199 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (22699259731 / 1000000000000 : ℝ))
      (E := (cell12554 ⟨35, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (41433547653199 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (22699259731 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_36 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82832927590287 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269929969329 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨36, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82832927590287 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269929969329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_37 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (331195134799 / 400000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567483497607 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨37, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (331195134799 / 400000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567483497607 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_38 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (41382331802109 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (453987595653 / 20000000000000 : ℝ))
      (E := (cell12554 ⟨38, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (41382331802109 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (453987595653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_39 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82730567273277 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269941991809 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨39, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82730567273277 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269941991809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12555_20 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83382482336687 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (226973757951 / 10000000000000 : ℝ))
      (E := (cell12555 ⟨20, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83382482336687 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (226973757951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_21 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41673976888563 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567435392503 / 25000000000000 : ℝ))
      (E := (cell12555 ⟨21, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41673976888563 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567435392503 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_22 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (10414181190061 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269745608853 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨22, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (10414181190061 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269745608853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_23 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83278969533763 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269749583443 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨23, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83278969533763 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269749583443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_24 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (8324451378411 / 10000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134876807101 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨24, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (8324451378411 / 10000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134876807101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_25 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83210082238859 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269757587973 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨25, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83210082238859 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269757587973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_26 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41587837432753 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269761566393 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨26, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41587837432753 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269761566393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_27 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83141291631713 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134882805479 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨27, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83141291631713 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134882805479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_28 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83106932505311 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269769607669 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨28, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83106932505311 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269769607669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_29 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (20768149363573 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269773559057 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨29, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (20768149363573 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269773559057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_30 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (16607657289363 / 20000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134888792209 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨30, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (16607657289363 / 20000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134888792209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_31 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83003999451199 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (56744539223 / 2500000000000 : ℝ))
      (E := (cell12555 ⟨31, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83003999451199 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (56744539223 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_32 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (82969736435927 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567446393237 / 25000000000000 : ℝ))
      (E := (cell12555 ⟨32, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (82969736435927 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567446393237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_33 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (82935497369641 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (283723699773 / 12500000000000 : ℝ))
      (E := (cell12555 ⟨33, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (82935497369641 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (283723699773 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_34 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (10362660277643 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269793587489 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨34, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (10362660277643 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269793587489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_35 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (20716772739849 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134898800319 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨35, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (20716772739849 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134898800319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_36 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (82832923553517 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269801579993 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨36, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (82832923553517 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269801579993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_37 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (82798779972783 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134902792461 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨37, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (82798779972783 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134902792461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_38 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41382330093313 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (113490480799 / 5000000000000 : ℝ))
      (E := (cell12555 ⟨38, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41382330093313 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (113490480799 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_39 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (10341320520579 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134906807393 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨39, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (10341320520579 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134906807393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12556_20 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83382473285759 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134804624973 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨20, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83382473285759 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134804624973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_21 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (10418493130367 / 12500000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134806606409 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨21, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (10418493130367 / 12500000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134806606409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_22 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83313441102593 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134808612373 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨22, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83313441102593 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134808612373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_23 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41639480715861 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (90784849259 / 4000000000000 : ℝ))
      (E := (cell12556 ⟨23, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41639480715861 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (90784849259 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_24 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (20811126499371 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269625236777 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨24, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (20811126499371 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269625236777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_25 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41605037383603 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (226962924419 / 10000000000000 : ℝ))
      (E := (cell12556 ⟨25, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41605037383603 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (226962924419 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_26 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (20793916927097 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567408314253 / 25000000000000 : ℝ))
      (E := (cell12556 ⟨26, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (20793916927097 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567408314253 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_27 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83141284788693 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134818609941 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨27, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83141284788693 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134818609941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_28 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83106925975951 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269641252467 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨28, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83106925975951 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269641252467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_29 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83072591238157 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269645240487 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨29, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83072591238157 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269645240487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_30 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83038280543469 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269649244741 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨30, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83038280543469 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269649244741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_31 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (5187749616263 / 6250000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453930641769 / 20000000000000 : ℝ))
      (E := (cell12556 ⟨31, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (5187749616263 / 6250000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453930641769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_32 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82969731156857 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269657251729 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨32, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82969731156857 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269657251729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_33 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82935492402059 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269661258009 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨33, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82935492402059 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269661258009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_34 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82901277564617 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134832614533 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨34, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82901277564617 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134832614533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_35 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (16573417322699 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (70927163271 / 3125000000000 : ℝ))
      (E := (cell12556 ⟨35, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (16573417322699 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (70927163271 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_36 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82832919517811 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (226967324583 / 10000000000000 : ℝ))
      (E := (cell12556 ⟨36, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82832919517811 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (226967324583 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_37 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41399388123421 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567419308663 / 25000000000000 : ℝ))
      (E := (cell12556 ⟨37, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41399388123421 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567419308663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_38 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82764656770021 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567420312577 / 25000000000000 : ℝ))
      (E := (cell12556 ⟨38, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82764656770021 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567420312577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_39 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (16546112211387 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (141855327151 / 6250000000000 : ℝ))
      (E := (cell12556 ⟨39, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (16546112211387 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (141855327151 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12557_20 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83382464236509 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453896183257 / 20000000000000 : ℝ))
      (E := (cell12557 ⟨20, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83382464236509 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453896183257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_21 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (16669587262077 / 20000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453896981971 / 20000000000000 : ℝ))
      (E := (cell12557 ⟨21, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (16669587262077 / 20000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453896981971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_22 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83313432686299 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453897778987 / 20000000000000 : ℝ))
      (E := (cell12557 ⟨22, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83313432686299 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453897778987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_23 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83278953331243 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269492933867 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨23, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83278953331243 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269492933867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_24 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (4162224910619 / 5000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (90779876551 / 4000000000000 : ℝ))
      (E := (cell12557 ⟨24, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (4162224910619 / 5000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (90779876551 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_25 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41605033648519 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (226950089651 / 10000000000000 : ℝ))
      (E := (cell12557 ⟨25, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41605033648519 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (226950089651 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_26 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (20793915138179 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134752471887 / 50000000000000 : ℝ))
      (E := (cell12557 ⟨26, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (20793915138179 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134752471887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_27 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (2078531948677 / 2500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453901788369 / 20000000000000 : ℝ))
      (E := (cell12557 ⟨27, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (2078531948677 / 2500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453901788369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_28 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (2077672986199 / 2500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269512893487 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨28, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (2077672986199 / 2500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269512893487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_29 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (10384073127919 / 12500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (113475845909 / 5000000000000 : ℝ))
      (E := (cell12557 ⟨29, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (10384073127919 / 12500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (113475845909 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_30 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (16607654928283 / 20000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567380225341 / 25000000000000 : ℝ))
      (E := (cell12557 ⟨30, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (16607654928283 / 20000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567380225341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_31 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (8300398827047 / 10000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (141845306477 / 6250000000000 : ℝ))
      (E := (cell12557 ⟨31, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (8300398827047 / 10000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (141845306477 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_32 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82969725879001 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269528926891 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨32, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82969725879001 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269528926891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_33 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82935487435653 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269532914253 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨33, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82935487435653 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269532914253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_34 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (8290127290923 / 10000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567384231423 / 25000000000000 : ℝ))
      (E := (cell12557 ⟨34, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (8290127290923 / 10000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567384231423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_35 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41433541134347 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (113477045191 / 5000000000000 : ℝ))
      (E := (cell12557 ⟨35, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41433541134347 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (113477045191 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_36 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82832915483167 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269544908203 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨36, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82832915483167 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269544908203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_37 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (3311950900877 / 4000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269548939621 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨37, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (3311950900877 / 4000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269548939621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_38 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82764653354403 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (70923529373 / 3125000000000 : ℝ))
      (E := (cell12557 ⟨38, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82764653354403 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (70923529373 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_39 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (20682639487547 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134778454703 / 50000000000000 : ℝ))
      (E := (cell12557 ⟨39, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (20682639487547 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134778454703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12558_20 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83382455188937 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567338159199 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨20, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83382455188937 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567338159199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_21 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83347927579473 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269356661127 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨21, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83347927579473 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269356661127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_22 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (16662684854321 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567340169433 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨22, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (16662684854321 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567340169433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_23 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41639472616163 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567341158071 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨23, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41639472616163 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567341158071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_24 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41622245214399 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269368645199 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨24, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41622245214399 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269368645199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_25 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83210059828353 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269372661699 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨25, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83210059828353 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269372661699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_26 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (8317565339849 / 10000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (56734415667 / 2500000000000 : ℝ))
      (E := (cell12558 ⟨26, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (8317565339849 / 10000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (56734415667 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_27 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41570635553437 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269380659993 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨27, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41570635553437 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269380659993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_28 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41553456460669 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453876929527 / 20000000000000 : ℝ))
      (E := (cell12558 ⟨28, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41553456460669 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453876929527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_29 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83072578809877 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269388650611 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨29, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83072578809877 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269388650611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_30 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (20759567185163 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269392671289 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨30, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (20759567185163 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269392671289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_31 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (16600796536397 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567349163321 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨31, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (16600796536397 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567349163321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_32 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (2074243015059 / 2500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269400656981 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨32, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (2074243015059 / 2500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269400656981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_33 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (10366935308803 / 12500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (283675585507 / 12500000000000 : ℝ))
      (E := (cell12558 ⟨33, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (10366935308803 / 12500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (283675585507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_34 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82901268254981 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567352169343 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨34, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82901268254981 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567352169343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_35 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41433538962497 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134706319041 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨35, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41433538962497 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134706319041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_36 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (16566582289917 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453883336879 / 20000000000000 : ℝ))
      (E := (cell12558 ⟨36, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (16566582289917 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453883336879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_37 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82798768798033 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134710320583 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨37, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82798768798033 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134710320583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_38 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82764649939771 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269424684867 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨38, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82764649939771 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269424684867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_39 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (20682638711097 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567357159941 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨39, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (20682638711097 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567357159941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12559_20 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83382446143043 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567306102869 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨20, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83382446143043 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567306102869 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_21 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83347918850199 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (453845681669 / 20000000000000 : ℝ))
      (E := (cell12559 ⟨21, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83347918850199 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (453845681669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_22 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (8331341585851 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (453846491303 / 20000000000000 : ℝ))
      (E := (cell12559 ⟨22, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (8331341585851 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (453846491303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_23 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83278937134969 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567309110849 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨23, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83278937134969 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567309110849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_24 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83244482646739 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567310107761 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨24, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83244482646739 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567310107761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_25 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (1300157068143 / 1562500000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269244422993 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨25, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (1300157068143 / 1562500000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269244422993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_26 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20793911561427 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269248422541 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨26, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20793911561427 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269248422541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_27 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41570632134037 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269252432753 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨27, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41570632134037 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269252432753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_28 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83106906396083 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134628228229 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨28, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83106906396083 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134628228229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_29 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83072572597731 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269260437781 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨29, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83072572597731 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269260437781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_30 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83038262841179 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567316109379 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨30, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83038262841179 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567316109379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_31 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (2593874284211 / 3125000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (11346342289 / 500000000000 : ℝ))
      (E := (cell12559 ⟨31, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (2593874284211 / 3125000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (11346342289 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_32 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41484857663467 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567318110499 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨32, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41484857663467 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567318110499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_33 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82935477506371 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (56731911257 / 2500000000000 : ℝ))
      (E := (cell12559 ⟨33, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82935477506371 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (56731911257 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_34 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (8290126360187 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (226928042551 / 10000000000000 : ℝ))
      (E := (cell12559 ⟨34, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (8290126360187 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (226928042551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_35 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41433536791197 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134642213729 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨35, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41433536791197 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134642213729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_36 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41416453708533 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134644228561 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨36, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41416453708533 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134644228561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_37 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20699691268791 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134646228307 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨37, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20699691268791 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134646228307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_38 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (662117172209 / 800000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567324106603 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨38, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (662117172209 / 800000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567324106603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_39 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82730551739537 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567325106371 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨39, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82730551739537 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567325106371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12560_20 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (3335297483953 / 4000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (226909624033 / 10000000000000 : ℝ))
      (E := (cell12560 ⟨20, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (3335297483953 / 4000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (226909624033 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_21 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (20836977530641 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269100268087 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨21, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (20836977530641 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269100268087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_22 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (16662681489403 / 20000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269104231287 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨22, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (16662681489403 / 20000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269104231287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_23 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (20819732259793 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269108250537 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨23, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (20819732259793 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269108250537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_24 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83244474866201 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567278067829 / 25000000000000 : ℝ))
      (E := (cell12560 ⟨24, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83244474866201 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567278067829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_25 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41605022447717 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (283639529847 / 12500000000000 : ℝ))
      (E := (cell12560 ⟨25, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41605022447717 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (283639529847 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_26 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83175639094371 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453824054591 / 20000000000000 : ℝ))
      (E := (cell12560 ⟨26, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83175639094371 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453824054591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_27 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (2078531435767 / 2500000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269124260129 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨27, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (2078531435767 / 2500000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269124260129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_28 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (16621379974439 / 20000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269128261509 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨28, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (16621379974439 / 20000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269128261509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_29 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41536283193457 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567283069923 / 25000000000000 : ℝ))
      (E := (cell12560 ⟨29, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41536283193457 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567283069923 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_30 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41519128471499 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269136258547 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨30, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41519128471499 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269136258547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_31 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (20750992877193 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269140258661 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨31, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (20750992877193 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269140258661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_32 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41484855026361 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134572111697 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨32, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41484855026361 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134572111697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_33 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (16587094508699 / 20000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134574135747 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨33, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (16587094508699 / 20000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134574135747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_34 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82901258949897 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269152228703 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨34, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82901258949897 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269152228703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_35 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82867069240893 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (141822266997 / 6250000000000 : ℝ))
      (E := (cell12560 ⟨35, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82867069240893 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (141822266997 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_36 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82832903385607 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269160285031 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨36, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82832903385607 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269160285031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_37 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82798761353319 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269164268641 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨37, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82798761353319 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269164268641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_38 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (16552928622693 / 20000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269168281949 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨38, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (16552928622693 / 20000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269168281949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_39 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41365274317817 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567293066643 / 25000000000000 : ℝ))
      (E := (cell12560 ⟨39, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41365274317817 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567293066643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12561_20 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (20845607014071 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134484061679 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨20, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (20845607014071 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134484061679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_21 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41673950698283 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134486061889 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨21, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41673950698283 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134486061889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_22 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41656699518559 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268976118671 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨22, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41656699518559 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268976118671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_23 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (10409865118117 / 12500000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268980112041 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨23, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (10409865118117 / 12500000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268980112041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_24 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (16648893417437 / 20000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (283623013457 / 12500000000000 : ℝ))
      (E := (cell12561 ⟨24, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (16648893417437 / 20000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (283623013457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_25 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41605018715599 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268988109049 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨25, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41605018715599 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268988109049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_26 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (83175631944477 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268992119517 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨26, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (83175631944477 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268992119517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_27 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (20785312648673 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (56724903553 / 2500000000000 : ℝ))
      (E := (cell12561 ⟨27, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (20785312648673 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (56724903553 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_28 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (3324275733987 / 4000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567250030309 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨28, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (3324275733987 / 4000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567250030309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_29 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41536280088713 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567251029467 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨29, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41536280088713 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567251029467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_30 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (83038251046107 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134504067191 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨30, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (83038251046107 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134504067191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_31 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (20750991481011 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567253028597 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨31, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (20750991481011 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567253028597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_32 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82969704779723 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226901611827 / 10000000000000 : ℝ))
      (E := (cell12561 ⟨32, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82969704779723 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226901611827 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_33 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82935467581793 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269020089133 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨33, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82935467581793 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269020089133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_34 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82901254299061 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (283628018193 / 12500000000000 : ℝ))
      (E := (cell12561 ⟨34, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82901254299061 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (283628018193 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_35 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (20716766225123 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269028112947 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨35, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (20716766225123 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269028112947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_36 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82832899355211 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134516054739 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨36, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82832899355211 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134516054739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_37 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41399378816249 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226903613591 / 10000000000000 : ℝ))
      (E := (cell12561 ⟨37, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41399378816249 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226903613591 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_38 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (8276463970179 / 10000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (283630016763 / 12500000000000 : ℝ))
      (E := (cell12561 ⟨38, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (8276463970179 / 10000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (283630016763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_39 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41365272766339 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567261026079 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨39, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41365272766339 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567261026079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12562_20 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41691209507709 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268840002297 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨20, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41691209507709 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268840002297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_21 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (16669578534441 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268844033707 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨21, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (16669578534441 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268844033707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_22 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (4165669531441 / 5000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567212000511 / 25000000000000 : ℝ))
      (E := (cell12562 ⟨22, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (4165669531441 / 5000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567212000511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_23 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83278912852259 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (226885202791 / 10000000000000 : ℝ))
      (E := (cell12562 ⟨23, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83278912852259 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (226885202791 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_24 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83244459309689 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (90754239937 / 4000000000000 : ℝ))
      (E := (cell12562 ⟨24, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83244459309689 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (90754239937 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_25 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (16642005993689 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268860033813 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨25, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (16642005993689 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268860033813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_26 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (20793906199007 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283608002579 / 12500000000000 : ℝ))
      (E := (cell12562 ⟨26, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (20793906199007 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283608002579 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_27 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (20785310940027 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (22688680203 / 1000000000000 : ℝ))
      (E := (cell12562 ⟨27, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (20785310940027 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (22688680203 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_28 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83106886828521 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (453774407129 / 20000000000000 : ℝ))
      (E := (cell12562 ⟨28, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83106886828521 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (453774407129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_29 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41536276984633 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567219002697 / 25000000000000 : ℝ))
      (E := (cell12562 ⟨29, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41536276984633 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567219002697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_30 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41519122575253 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268880006523 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨30, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41519122575253 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268880006523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_31 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83003960340567 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283610503123 / 12500000000000 : ℝ))
      (E := (cell12562 ⟨31, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83003960340567 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283610503123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_32 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41484849753969 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268888009529 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨32, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41484849753969 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268888009529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_33 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82935462621267 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134446010167 / 50000000000000 : ℝ))
      (E := (cell12562 ⟨33, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82935462621267 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134446010167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_34 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41450624824681 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (453779200051 / 20000000000000 : ℝ))
      (E := (cell12562 ⟨34, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41450624824681 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (453779200051 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_35 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82867060561189 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268900009061 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨35, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82867060561189 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268900009061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_36 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (662663162607 / 800000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268904047747 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨36, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (662663162607 / 800000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268904047747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_37 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82798753912699 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268908058423 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨37, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82798753912699 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268908058423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_38 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (827646362911 / 1000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (453782408313 / 20000000000000 : ℝ))
      (E := (cell12562 ⟨38, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (827646362911 / 1000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (453782408313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_39 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (8273054243067 / 10000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134458028069 / 50000000000000 : ℝ))
      (E := (cell12562 ⟨39, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (8273054243067 / 10000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134458028069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12563_20 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83382409976229 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (90748479747 / 4000000000000 : ℝ))
      (E := (cell12563 ⟨20, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83382409976229 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (90748479747 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_21 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83347883949481 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567178999469 / 25000000000000 : ℝ))
      (E := (cell12563 ⟨21, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83347883949481 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567178999469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_22 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83313382222119 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (141794999877 / 6250000000000 : ℝ))
      (E := (cell12563 ⟨22, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83313382222119 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (141794999877 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_23 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41639452380571 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268723998143 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨23, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41639452380571 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268723998143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_24 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41622225766857 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (113436400099 / 5000000000000 : ℝ))
      (E := (cell12563 ⟨24, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41622225766857 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (113436400099 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_25 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83210022507173 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268731954687 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨25, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83210022507173 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268731954687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_26 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41587808824511 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134367988151 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨26, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41587808824511 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134367988151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_27 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (8314123692693 / 10000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268739953097 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨27, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (8314123692693 / 10000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268739953097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_28 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41553440154367 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134372002367 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨28, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41553440154367 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134372002367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_29 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41536273881217 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268747958451 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨29, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41536273881217 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268747958451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_30 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41519119628097 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (226875199197 / 10000000000000 : ℝ))
      (E := (cell12563 ⟨30, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41519119628097 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (226875199197 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_31 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41501977379171 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268755990449 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨31, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41501977379171 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268755990449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_32 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41484847118683 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (56718998893 / 2500000000000 : ℝ))
      (E := (cell12563 ⟨32, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41484847118683 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (56718998893 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_33 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (20733864415479 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (226876400653 / 10000000000000 : ℝ))
      (E := (cell12563 ⟨33, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (20733864415479 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (226876400653 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_34 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (103626556251 / 125000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (283595996077 / 12500000000000 : ℝ))
      (E := (cell12563 ⟨34, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (103626556251 / 125000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (283595996077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_35 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41433528111493 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134385980147 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨35, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41433528111493 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134385980147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_36 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (51770557061 / 62500000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134387991279 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨36, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (51770557061 / 62500000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134387991279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_37 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (82798750193923 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268779977517 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨37, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (82798750193923 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268779977517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_38 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (16552926576279 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268784004333 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨38, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (16552926576279 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268784004333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_39 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (82730539329609 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268788004619 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨39, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (82730539329609 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268788004619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12564_20 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41691200469357 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268583980967 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨20, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41691200469357 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268583980967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_21 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83347875228393 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134293978999 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨21, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83347875228393 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134293978999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_22 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (10414171727127 / 12500000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268591990013 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨22, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (10414171727127 / 12500000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268591990013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_23 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83278896671583 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268595964411 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨23, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83278896671583 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268595964411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_24 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83244443759259 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (9074399773 / 400000000000 : ℝ))
      (E := (cell12564 ⟨24, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83244443759259 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (9074399773 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_25 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83210015047383 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134301994219 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨25, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83210015047383 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134301994219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_26 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41587805251729 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (226860798653 / 10000000000000 : ℝ))
      (E := (cell12564 ⟨26, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41587805251729 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (226860798653 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_27 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (20785307523789 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268611998943 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨27, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (20785307523789 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268611998943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_28 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (10388359223789 / 12500000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134307985027 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨28, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (10388359223789 / 12500000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134307985027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_29 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83072541556929 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268619960861 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨29, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83072541556929 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268619960861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_30 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (20759558340793 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134311986863 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨30, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (20759558340793 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134311986863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_31 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (10375493647171 / 12500000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134313976131 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨31, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (10375493647171 / 12500000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134313976131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_32 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82969688968007 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134315978423 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨32, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82969688968007 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134315978423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_33 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82935452703739 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268635989153 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨33, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82935452703739 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268635989153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_34 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41450620176687 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268639992037 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨34, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41450620176687 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268639992037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_35 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82867051885881 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (283580495831 / 12500000000000 : ℝ))
      (E := (cell12564 ⟨35, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82867051885881 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (283580495831 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_36 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (16566577454077 / 20000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268647972553 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨36, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (16566577454077 / 20000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268647972553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_37 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (8279874647617 / 10000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (141790746991 / 6250000000000 : ℝ))
      (E := (cell12564 ⟨37, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (8279874647617 / 10000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (141790746991 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_38 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (3310585178907 / 4000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134327981861 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨38, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (3310585178907 / 4000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134327981861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_39 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41365268114747 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (283582501059 / 12500000000000 : ℝ))
      (E := (cell12564 ⟨39, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41365268114747 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (283582501059 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12565_20 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (667059135223 / 800000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134228011219 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨20, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (667059135223 / 800000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134228011219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_21 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83347866508941 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268460030651 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨21, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83347866508941 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268460030651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_22 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83313365413511 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268464036299 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨22, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83313365413511 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268464036299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_23 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41639444291791 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (283558498131 / 12500000000000 : ℝ))
      (E := (cell12565 ⟨23, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41639444291791 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (283558498131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_24 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (20811108996581 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (226847199731 / 10000000000000 : ℝ))
      (E := (cell12565 ⟨24, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (20811108996581 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (226847199731 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_25 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41605003794537 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268476018301 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨25, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41605003794537 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268476018301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_26 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83175603359337 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (226847999291 / 10000000000000 : ℝ))
      (E := (cell12565 ⟨26, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83175603359337 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (226847999291 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_27 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (16628244652957 / 20000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134241991277 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨27, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (16628244652957 / 20000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134241991277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_28 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (10388358409157 / 12500000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134243995029 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨28, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (10388358409157 / 12500000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134243995029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_29 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (5192033459547 / 6250000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (70890375563 / 3125000000000 : ℝ))
      (E := (cell12565 ⟨29, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (5192033459547 / 6250000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (70890375563 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_30 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41519113735719 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268496010293 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨30, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41519113735719 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268496010293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_31 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (20750985899411 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268500027471 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨31, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (20750985899411 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268500027471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_32 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (4148484184993 / 5000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134252006453 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨32, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (4148484184993 / 5000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134252006453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_33 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82935447746737 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268508026773 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨33, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82935447746737 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268508026773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_34 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (16580247141417 / 20000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567128002981 / 25000000000000 : ℝ))
      (E := (cell12565 ⟨34, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (16580247141417 / 20000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567128002981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_35 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41433523774937 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134258014063 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨35, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41433523774937 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134258014063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_36 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (8283288324423 / 10000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268520017733 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨36, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (8283288324423 / 10000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268520017733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_37 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82798742759439 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268524040107 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨37, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82798742759439 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268524040107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_38 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82764626064939 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567132009277 / 25000000000000 : ℝ))
      (E := (cell12565 ⟨38, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82764626064939 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567132009277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_39 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41365266565163 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (453706401797 / 20000000000000 : ℝ))
      (E := (cell12565 ⟨39, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41365266565163 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (453706401797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12566_20 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83382382868709 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268328118089 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨20, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83382382868709 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268328118089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_21 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (666782862329 / 800000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134166049629 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨21, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (666782862329 / 800000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134166049629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_22 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (41656678505801 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134168039289 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨22, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (41656678505801 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134168039289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_23 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (4163944024857 / 5000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268340118387 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨23, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (4163944024857 / 5000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268340118387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_24 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20811107053727 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134172052901 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨24, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20811107053727 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134172052901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_25 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (41605000066123 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268348102659 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨25, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (41605000066123 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268348102659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_26 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83175596216659 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567088028063 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨26, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83175596216659 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567088028063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_27 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83141216435819 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567089019803 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨27, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83141216435819 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567089019803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_28 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (16621372151513 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (453672012949 / 20000000000000 : ℝ))
      (E := (cell12566 ⟨28, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (16621372151513 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (453672012949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_29 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83072529149901 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268364071443 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨29, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83072529149901 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268364071443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_30 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83038221580993 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567092025417 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨30, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83038221580993 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567092025417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_31 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83003938019171 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567093024757 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨31, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83003938019171 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567093024757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_32 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (3318787137317 / 4000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (453675213071 / 20000000000000 : ℝ))
      (E := (cell12566 ⟨32, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (3318787137317 / 4000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (453675213071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_33 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20733860697727 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (226838011939 / 10000000000000 : ℝ))
      (E := (cell12566 ⟨33, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20733860697727 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (226838011939 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_34 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (82901231061931 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268384086871 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨34, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (82901231061931 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268384086871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_35 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20716760803741 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268388086109 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨35, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20716760803741 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268388086109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_36 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (1294263737799 / 1562500000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268392118097 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨36, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (1294263737799 / 1562500000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268392118097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_37 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (8279873904373 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268396124941 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨37, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (8279873904373 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268396124941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_38 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20691155664547 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134200053557 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨38, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20691155664547 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134200053557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_39 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (10341316254013 / 12500000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268404123581 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨39, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (10341316254013 / 12500000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268404123581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12567_20 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41691186918109 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (283525026207 / 12500000000000 : ℝ))
      (E := (cell12567 ⟨20, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41691186918109 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (283525026207 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_21 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83347849074943 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268204222111 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨21, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83347849074943 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268204222111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_22 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83313348611289 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (56705205837 / 2500000000000 : ℝ))
      (E := (cell12567 ⟨22, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83313348611289 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (56705205837 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_23 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (16655774482451 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268212189429 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨23, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (16655774482451 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268212189429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_24 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (20811105111253 / 25000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268216210369 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨24, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (20811105111253 / 25000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268216210369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_25 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41604996338449 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (453644048303 / 20000000000000 : ℝ))
      (E := (cell12567 ⟨25, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41604996338449 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (453644048303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_26 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41587794537711 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268224227751 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨26, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41587794537711 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268224227751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_27 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (1299081400129 / 1562500000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (70882132203 / 3125000000000 : ℝ))
      (E := (cell12567 ⟨27, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (1299081400129 / 1562500000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (70882132203 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_28 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (2077671356081 / 2500000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268232194119 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨28, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (2077671356081 / 2500000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268232194119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_29 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83072522948377 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (453647247619 / 20000000000000 : ℝ))
      (E := (cell12567 ⟨29, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83072522948377 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (453647247619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_30 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83038215691837 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (453648037871 / 20000000000000 : ℝ))
      (E := (cell12567 ⟨30, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83038215691837 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (453648037871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_31 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83003932441947 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268244225461 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨31, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83003932441947 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268244225461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_32 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41484836583601 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268248231287 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨32, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41484836583601 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268248231287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_33 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82935437836253 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134126104219 / 50000000000000 : ℝ))
      (E := (cell12567 ⟨33, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82935437836253 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134126104219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_34 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82901226417913 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268256216881 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨34, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82901226417913 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268256216881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_35 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (647398741259 / 781250000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268260199217 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨35, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (647398741259 / 781250000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268260199217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_36 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (828328751951 / 1000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (226826421501 / 10000000000000 : ℝ))
      (E := (cell12567 ⟨36, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (828328751951 / 1000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (226826421501 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_37 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41399367664521 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134134103181 / 50000000000000 : ℝ))
      (E := (cell12567 ⟨37, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41399367664521 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134134103181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_38 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82764619252419 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567068058109 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨38, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82764619252419 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567068058109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_39 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82730526934829 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268276234839 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨39, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82730526934829 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268276234839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12568_20 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (416911824027 / 500000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268072413671 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨20, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (416911824027 / 500000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268072413671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_21 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (20836960090099 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268076399209 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨21, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (20836960090099 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268076399209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_22 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (20828335053143 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268080384377 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨22, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (20828335053143 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268080384377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_23 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83278864328927 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134042186589 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨23, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83278864328927 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134042186589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_24 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83244412676633 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268088369373 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨24, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83244412676633 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268088369373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_25 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (8320998522303 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268092376487 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨25, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (8320998522303 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268092376487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_26 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (41587790967813 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567024099453 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨26, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (41587790967813 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567024099453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_27 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (5196325173881 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134050188987 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨27, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (5196325173881 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134050188987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_28 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (41553423865139 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (113405218909 / 5000000000000 : ℝ))
      (E := (cell12568 ⟨28, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (41553423865139 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (113405218909 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_29 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (4153625837409 / 5000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (113405420051 / 5000000000000 : ℝ))
      (E := (cell12568 ⟨29, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (4153625837409 / 5000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (113405420051 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_30 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (1297472028187 / 1562500000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (453622478071 / 20000000000000 : ℝ))
      (E := (cell12568 ⟨30, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (1297472028187 / 1562500000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (453622478071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_31 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (41501963432987 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (141757275423 / 6250000000000 : ℝ))
      (E := (cell12568 ⟨31, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (41501963432987 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (141757275423 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_32 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (8296966790269 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567030098403 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨32, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (8296966790269 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567030098403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_33 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (20733858220693 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (141757775691 / 6250000000000 : ℝ))
      (E := (cell12568 ⟨33, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (20733858220693 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (141757775691 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_34 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (8290122177503 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268128401953 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨34, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (8290122177503 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268128401953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_35 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (41433517274219 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (45362647349 / 2000000000000 : ℝ))
      (E := (cell12568 ⟨35, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (41433517274219 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (45362647349 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_36 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (20708217793031 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268136367109 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨36, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (20708217793031 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268136367109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_37 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (5174920725961 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (70879387553 / 3125000000000 : ℝ))
      (E := (cell12568 ⟨37, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (5174920725961 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (70879387553 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_38 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (16552923169527 / 20000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567036103267 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨38, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (16552923169527 / 20000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567036103267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_39 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (41365261919249 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134074200737 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨39, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (41365261919249 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134074200737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12569_20 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (16676471155251 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453588922721 / 20000000000000 : ℝ))
      (E := (cell12569 ⟨20, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (16676471155251 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453588922721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_21 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (20836957911871 / 25000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453589714453 / 20000000000000 : ℝ))
      (E := (cell12569 ⟨21, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (20836957911871 / 25000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453589714453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_22 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (1666266636309 / 2000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133976294793 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨22, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (1666266636309 / 2000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133976294793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_23 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (20819714061789 / 25000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (22679566113 / 1000000000000 : ℝ))
      (E := (cell12569 ⟨23, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (20819714061789 / 25000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (22679566113 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_24 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83244404909773 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (566990145703 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨24, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83244404909773 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (566990145703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_25 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41604988885321 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267964624341 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨25, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41604988885321 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267964624341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_26 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (10396946849659 / 12500000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133984311217 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨26, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (10396946849659 / 12500000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133984311217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_27 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41570597978669 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267972580077 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨27, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41570597978669 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267972580077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_28 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83106841218681 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226797661693 / 10000000000000 : ℝ))
      (E := (cell12569 ⟨28, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83106841218681 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226797661693 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_29 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83072510549307 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133990309349 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨29, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83072510549307 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133990309349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_30 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41519101958693 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226798458767 / 10000000000000 : ℝ))
      (E := (cell12569 ⟨30, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41519101958693 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226798458767 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_31 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83003921291249 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267988584429 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨31, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83003921291249 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267988584429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_32 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (8296966263939 / 10000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133996305437 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨32, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (8296966263939 / 10000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133996305437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_33 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82935427930463 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133998305053 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨33, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82935427930463 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133998305053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_34 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41450608566641 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (283500072937 / 12500000000000 : ℝ))
      (E := (cell12569 ⟨34, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41450608566641 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (283500072937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_35 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (4143351510841 / 5000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226800459081 / 10000000000000 : ℝ))
      (E := (cell12569 ⟨35, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (4143351510841 / 5000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226800459081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_36 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82832867150207 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268008574397 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨36, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82832867150207 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268008574397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_37 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (8279872790273 / 10000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134006296809 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨37, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (8279872790273 / 10000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134006296809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_38 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82764612443833 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268016590327 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨38, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82764612443833 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268016590327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_39 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82730520743113 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567005155871 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨39, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82730520743113 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567005155871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12570_20 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41691173374391 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566954216931 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨20, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41691173374391 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566954216931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_21 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (16669564587241 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133910428929 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨21, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (16669564587241 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133910428929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_22 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (20828330854981 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (141739053069 / 6250000000000 : ℝ))
      (E := (cell12570 ⟨22, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (20828330854981 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (141739053069 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_23 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (83278848166941 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133914422731 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨23, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (83278848166941 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133914422731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_24 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (8324439714443 / 10000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226783285069 / 10000000000000 : ℝ))
      (E := (cell12570 ⟨24, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (8324439714443 / 10000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226783285069 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_25 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (83209970319733 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (283479608539 / 12500000000000 : ℝ))
      (E := (cell12570 ⟨25, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (83209970319733 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (283479608539 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_26 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41587783830179 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133920421607 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨26, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41587783830179 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133920421607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_27 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41570594566991 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (283480604601 / 12500000000000 : ℝ))
      (E := (cell12570 ⟨27, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41570594566991 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (283480604601 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_28 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (2597088584639 / 3125000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (453569770383 / 20000000000000 : ℝ))
      (E := (cell12570 ⟨28, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (2597088584639 / 3125000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (453569770383 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_29 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (83072504351761 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267852832649 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨29, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (83072504351761 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267852832649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_30 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (20759549508023 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267856839799 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨30, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (20759549508023 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267856839799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_31 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (83003915717773 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267860875491 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨31, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (83003915717773 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267860875491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_32 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (829696573773 / 1000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226786482453 / 10000000000000 : ℝ))
      (E := (cell12570 ⟨32, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (829696573773 / 1000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226786482453 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_33 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (82935422979327 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267868864157 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨33, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (82935422979327 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267868864157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_34 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (20725303123167 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267872878699 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨34, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (20725303123167 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267872878699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_35 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41433512943149 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133938434649 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨35, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41433512943149 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133938434649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_36 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (20708215782337 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566970209219 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨36, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (20708215782337 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566970209219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_37 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41399362095553 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267884840791 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨37, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41399362095553 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267884840791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_38 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41382304520507 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566972220397 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨38, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41382304520507 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566972220397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_39 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (82730517648673 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267892842159 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨39, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (82730517648673 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267892842159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12571_20 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41691168861491 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267689176029 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨20, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41691168861491 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267689176029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_21 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (130230959729 / 156250000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267693139411 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨21, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (130230959729 / 156250000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267693139411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_22 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (10414164378249 / 12500000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (283462145367 / 12500000000000 : ℝ))
      (E := (cell12571 ⟨22, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (10414164378249 / 12500000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (283462145367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_23 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83278840088283 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133850566999 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨23, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83278840088283 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133850566999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_24 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (16648877876121 / 20000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (453541034601 / 20000000000000 : ℝ))
      (E := (cell12571 ⟨24, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (16648877876121 / 20000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (453541034601 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_25 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41604981435151 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133854583393 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨25, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41604981435151 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133854583393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_26 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (20793890131221 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (453542635393 / 20000000000000 : ℝ))
      (E := (cell12571 ⟨26, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (20793890131221 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (453542635393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_27 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83141182312029 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566929287041 / 25000000000000 : ℝ))
      (E := (cell12571 ⟨27, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83141182312029 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566929287041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_28 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41553414099789 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267721141591 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨28, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41553414099789 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267721141591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_29 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83072498155539 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (283465644979 / 12500000000000 : ℝ))
      (E := (cell12571 ⟨29, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83072498155539 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (283465644979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_30 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (20759548037021 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (283466143343 / 12500000000000 : ℝ))
      (E := (cell12571 ⟨30, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (20759548037021 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (283466143343 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_31 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41501955072773 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566933290727 / 25000000000000 : ℝ))
      (E := (cell12571 ⟨31, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41501955072773 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566933290727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_32 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (4148482605821 / 5000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (90709486067 / 4000000000000 : ℝ))
      (E := (cell12571 ⟨32, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (4148482605821 / 5000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (90709486067 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_33 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82935418029363 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133870586607 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨33, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82935418029363 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133870586607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_34 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82901207853189 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267745170373 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨34, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82901207853189 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267745170373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_35 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82867021556873 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267749144297 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨35, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82867021556873 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267749144297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_36 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (20708214777387 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (453550630909 / 20000000000000 : ℝ))
      (E := (cell12571 ⟨36, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (20708214777387 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (453550630909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_37 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82798720480501 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267757143219 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨37, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82798720480501 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267757143219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_38 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41382302819589 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566940292369 / 25000000000000 : ℝ))
      (E := (cell12571 ⟨38, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41382302819589 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566940292369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_39 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41365257277589 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566941293731 / 25000000000000 : ℝ))
      (E := (cell12571 ⟨39, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41365257277589 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566941293731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12572_20 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83382328698853 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (35430648129 / 1562500000000 : ℝ))
      (E := (cell12572 ⟨20, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83382328698853 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (35430648129 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_21 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (20836951379637 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (141722842201 / 6250000000000 : ℝ))
      (E := (cell12572 ⟨21, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (20836951379637 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (141722842201 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_22 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (16662661326731 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267569472769 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨22, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (16662661326731 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267569472769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_23 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83278832011179 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267573476913 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨23, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83278832011179 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267573476913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_24 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83244381618297 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133788745701 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨24, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83244381618297 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133788745701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_25 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (1664199108447 / 2000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (113379073069 / 5000000000000 : ℝ))
      (E := (cell12572 ⟨25, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (1664199108447 / 2000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (113379073069 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_26 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (1663511067817 / 2000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566896376719 / 25000000000000 : ℝ))
      (E := (cell12572 ⟨26, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (1663511067817 / 2000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566896376719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_27 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (20785293872869 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (283448689269 / 12500000000000 : ℝ))
      (E := (cell12572 ⟨27, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (20785293872869 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (283448689269 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_28 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83106821692071 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267593485959 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨28, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83106821692071 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267593485959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_29 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41536245980321 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566899370823 / 25000000000000 : ℝ))
      (E := (cell12572 ⟨29, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41536245980321 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566899370823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_30 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83038186265363 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133800754253 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨30, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83038186265363 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133800754253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_31 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83003904574567 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453521101041 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨31, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83003904574567 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453521101041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_32 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82969646856751 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453521895043 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨32, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82969646856751 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453521895043 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_33 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82935413080571 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453522695741 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨33, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82935413080571 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453522695741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_34 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (20725300803711 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453523503423 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨34, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (20725300803711 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453523503423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_35 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (323699286049 / 390625000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133810737213 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨35, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (323699286049 / 390625000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133810737213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_36 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41416427545403 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133812734383 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨36, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41416427545403 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133812734383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_37 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82798716770917 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267629500901 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨37, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82798716770917 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267629500901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_38 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (20691150559581 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267633512683 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨38, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (20691150559581 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267633512683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_39 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (20682627865657 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566909376089 / 25000000000000 : ℝ))
      (E := (cell12572 ⟨39, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (20682627865657 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566909376089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12573_20 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (20845579919099 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133716948469 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨20, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (20845579919099 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133716948469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_21 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (10418474601521 / 12500000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267437865273 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨21, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (10418474601521 / 12500000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267437865273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_22 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83313298242911 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267441895231 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨22, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83313298242911 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267441895231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_23 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83278823935631 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (453489174841 / 20000000000000 : ℝ))
      (E := (cell12573 ⟨23, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83278823935631 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (453489174841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_24 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (16648874771501 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267449864241 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨24, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (16648874771501 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267449864241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_25 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (20802486993969 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133726934431 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨25, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (20802486993969 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133726934431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_26 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (5198471641141 / 6250000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133728945677 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨26, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (5198471641141 / 6250000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133728945677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_27 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (3325646746893 / 4000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267461876339 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨27, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (3325646746893 / 4000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267461876339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_28 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (41553407592963 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267465885021 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨28, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (41553407592963 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267465885021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_29 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (8307248576707 / 10000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566867465377 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨29, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (8307248576707 / 10000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566867465377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_30 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (10379772547991 / 12500000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267473866587 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨30, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (10379772547991 / 12500000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267473866587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_31 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (20750974751209 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (141717368899 / 6250000000000 : ℝ))
      (E := (cell12573 ⟨31, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (20750974751209 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (141717368899 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_32 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82969641598291 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267481853699 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨32, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82969641598291 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267481853699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_33 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (1658708162659 / 2000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267485897773 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨33, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (1658708162659 / 2000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267485897773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_34 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (2590662455551 / 3125000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566872465083 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨34, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (2590662455551 / 3125000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566872465083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_35 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82867012901311 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133746929843 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨35, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82867012901311 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133746929843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_36 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82832851073121 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133748948411 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨36, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82832851073121 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133748948411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_37 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82798713062353 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (90700074207 / 4000000000000 : ℝ))
      (E := (cell12573 ⟨37, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82798713062353 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (90700074207 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_38 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82764598838453 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133752926259 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨38, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82764598838453 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133752926259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_39 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82730508371021 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (226750988917 / 10000000000000 : ℝ))
      (E := (cell12573 ⟨39, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82730508371021 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (226750988917 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12574_20 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (8338231065561 / 10000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267306309543 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨20, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (8338231065561 / 10000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267306309543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_21 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (4167389405371 / 5000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267310309583 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨21, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (4167389405371 / 5000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267310309583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_22 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83313289853761 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (70853572303 / 3125000000000 : ℝ))
      (E := (cell12574 ⟨22, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83313289853761 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (70853572303 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_23 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41639407930819 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267318325877 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨23, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41639407930819 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267318325877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_24 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83244366098229 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267322291523 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨24, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83244366098229 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267322291523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_25 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83209940530879 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133663136233 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨25, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83209940530879 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133663136233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_26 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83175539127101 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133665135997 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨26, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83175539127101 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133665135997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_27 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41570580927287 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133667146579 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨27, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41570580927287 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133667146579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_28 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (16621361736229 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133669140161 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨28, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (16621361736229 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133669140161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_29 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83072479574821 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133671147241 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨29, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83072479574821 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133671147241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_30 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83038174503779 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267346279487 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨30, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83038174503779 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267346279487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_31 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (1296935834943 / 1562500000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267350295921 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨31, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (1296935834943 / 1562500000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267350295921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_32 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82969636341041 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (283419285891 / 12500000000000 : ℝ))
      (E := (cell12574 ⟨32, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82969636341041 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (283419285891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_33 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82935403186501 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133679156639 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨33, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82935403186501 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133679156639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_34 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82901193941553 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133681158607 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨34, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82901193941553 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133681158607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_35 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (20716752143793 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267366300079 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨35, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (20716752143793 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267366300079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_36 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41416423528247 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (283421290179 / 12500000000000 : ℝ))
      (E := (cell12574 ⟨36, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41416423528247 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (283421290179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_37 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (10349838669351 / 12500000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (226737432337 / 10000000000000 : ℝ))
      (E := (cell12574 ⟨37, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (10349838669351 / 12500000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (226737432337 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_38 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41382297719781 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133689153181 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨38, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41382297719781 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133689153181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_39 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82730505280359 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566845582341 / 25000000000000 : ℝ))
      (E := (cell12574 ⟨39, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82730505280359 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566845582341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

end BstLean.Part268
