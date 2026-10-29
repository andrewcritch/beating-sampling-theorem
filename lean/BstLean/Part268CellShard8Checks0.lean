import BstLean.Part268CellShard8Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12550_0 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (84078286966331 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454060016899 / 20000000000000 : ℝ))
      (E := (cell12550 ⟨0, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (84078286966331 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454060016899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_1 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (16808652703019 / 20000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270304089873 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨1, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (16808652703019 / 20000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270304089873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_2 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (10501033133339 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135154032147 / 50000000000000 : ℝ))
      (E := (cell12550 ⟨2, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (10501033133339 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135154032147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_3 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (5248330724033 / 6250000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (4434203271 / 195312500000 : ℝ))
      (E := (cell12550 ⟨3, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (5248330724033 / 6250000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (4434203271 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_4 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83938343032083 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135158036149 / 50000000000000 : ℝ))
      (E := (cell12550 ⟨4, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83938343032083 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135158036149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_5 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83903419373109 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270320065541 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨5, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83903419373109 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270320065541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_6 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83868520571529 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270324062837 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨6, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83868520571529 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270324062837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_7 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83833646591457 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (56758201807 / 2500000000000 : ℝ))
      (E := (cell12550 ⟨7, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83833646591457 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (56758201807 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_8 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (10474849674649 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567583010933 / 25000000000000 : ℝ))
      (E := (cell12550 ⟨8, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (10474849674649 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567583010933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_9 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (10470496619153 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135168021359 / 50000000000000 : ℝ))
      (E := (cell12550 ⟨9, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (10470496619153 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135168021359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_10 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41864586612113 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270340018543 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨10, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41864586612113 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270340018543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_11 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41847199087529 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567586009069 / 25000000000000 : ℝ))
      (E := (cell12550 ⟨11, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41847199087529 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567586009069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_12 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41829823885381 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (90813921787 / 4000000000000 : ℝ))
      (E := (cell12550 ⟨12, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41829823885381 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (90813921787 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_13 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41812460988281 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270352050257 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨13, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41812460988281 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270352050257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_14 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (16718044151573 / 20000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (283794507411 / 12500000000000 : ℝ))
      (E := (cell12550 ⟨14, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (16718044151573 / 20000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (283794507411 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_15 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83555544080257 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135180009821 / 50000000000000 : ℝ))
      (E := (cell12550 ⟨15, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83555544080257 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135180009821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_16 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83520891909503 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454072810673 / 20000000000000 : ℝ))
      (E := (cell12550 ⟨16, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83520891909503 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454072810673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_17 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (16697252842309 / 20000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (227036804967 / 10000000000000 : ℝ))
      (E := (cell12550 ⟨17, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (16697252842309 / 20000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (227036804967 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_18 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (83451660952501 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (90814880551 / 4000000000000 : ℝ))
      (E := (cell12550 ⟨18, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (83451660952501 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (90814880551 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_19 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (20854270524667 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567594002223 / 25000000000000 : ℝ))
      (E := (cell12550 ⟨19, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (20854270524667 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (567594002223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12551_0 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (84078271474001 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (283771437703 / 12500000000000 : ℝ))
      (E := (cell12551 ⟨0, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (84078271474001 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (283771437703 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_1 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (16808649669749 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270175464227 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨1, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (16808649669749 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270175464227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_2 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (2100206255647 / 2500000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567544878073 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨2, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (2100206255647 / 2500000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567544878073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_3 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83973277068753 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135091740747 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨3, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83973277068753 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135091740747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_4 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (16787665768181 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270187496407 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨4, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (16787665768181 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270187496407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_5 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (8390340550607 / 10000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270191507797 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨5, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (8390340550607 / 10000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270191507797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_6 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (20967126757043 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270195466083 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨6, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (20967126757043 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270195466083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_7 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (20958408342831 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270199495207 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨7, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (20958408342831 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270199495207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_8 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (20949696124957 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270203487119 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨8, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (20949696124957 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270203487119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_9 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (3350558415127 / 4000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270207449333 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨9, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (3350558415127 / 4000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270207449333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_10 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41864580485519 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (454042289429 / 20000000000000 : ℝ))
      (E := (cell12551 ⟨10, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41864580485519 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (454042289429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_11 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83694386243277 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270215487641 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨11, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83694386243277 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270215487641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_12 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83659636159937 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (4540438923 / 200000000000 : ℝ))
      (E := (cell12551 ⟨12, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83659636159937 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (4540438923 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_13 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83624910686243 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135111745683 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨13, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83624910686243 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135111745683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_14 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41795104893801 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (227022746733 / 10000000000000 : ℝ))
      (E := (cell12551 ⟨14, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41795104893801 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (227022746733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_15 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (104444416787 / 125000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270231453489 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨15, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (104444416787 / 125000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270231453489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_16 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (16704176315601 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (17736214497 / 781250000000 : ℝ))
      (E := (cell12551 ⟨16, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (16704176315601 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (17736214497 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_17 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41743127099379 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270239479241 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨17, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41743127099379 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270239479241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_18 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (4172582562899 / 5000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135121735717 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨18, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (4172582562899 / 5000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135121735717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_19 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (83417072721967 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270247437167 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨19, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (83417072721967 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270247437167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12552_0 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (84078255984143 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454008594327 / 20000000000000 : ℝ))
      (E := (cell12552 ⟨0, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (84078255984143 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454008594327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_1 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (42021616592413 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454009389869 / 20000000000000 : ℝ))
      (E := (cell12552 ⟨1, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (42021616592413 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454009389869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_2 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (84008235387439 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270050955459 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨2, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (84008235387439 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270050955459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_3 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83973262555329 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270054941311 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨3, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83973262555329 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270054941311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_4 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83938314652039 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135029486827 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨4, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83938314652039 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135029486827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_5 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83903391641303 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (35469733521 / 1562500000000 : ℝ))
      (E := (cell12552 ⟨5, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83903391641303 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (35469733521 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_6 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41934246743523 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270066922597 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨6, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41934246743523 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270066922597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_7 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83833620153383 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567517742867 / 25000000000000 : ℝ))
      (E := (cell12552 ⟨7, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83833620153383 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567517742867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_8 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83798771604617 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270074925919 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨8, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83798771604617 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270074925919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_9 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41881973902619 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454015793483 / 20000000000000 : ℝ))
      (E := (cell12552 ⟨9, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41881973902619 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454015793483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_10 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41864574359961 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270082929273 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨10, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41864574359961 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270082929273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_11 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (8369437431353 / 10000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135043467271 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨11, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (8369437431353 / 10000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135043467271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_12 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83659624551107 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (283761366497 / 12500000000000 : ℝ))
      (E := (cell12552 ⟨12, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83659624551107 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (283761366497 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_13 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83624899397879 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270094928091 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨13, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83624899397879 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270094928091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_14 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41795099409627 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270098929153 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨14, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41795099409627 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270098929153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_15 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (4177776139041 / 5000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270102941179 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨15, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (4177776139041 / 5000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270102941179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_16 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83520871248343 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (90804276471 / 4000000000000 : ℝ))
      (E := (cell12552 ⟨16, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83520871248343 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (90804276471 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_17 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (83486244187769 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (227011090459 / 10000000000000 : ℝ))
      (E := (cell12552 ⟨17, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (83486244187769 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (227011090459 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_18 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41725820782609 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270114924911 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨18, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41725820782609 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270114924911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_19 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41708531673493 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270118919539 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨19, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41708531673493 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270118919539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12553_0 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (21019560124189 / 25000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269914494529 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨0, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (21019560124189 / 25000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269914494529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_1 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (42021609011669 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567479621853 / 25000000000000 : ℝ))
      (E := (cell12553 ⟨1, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (42021609011669 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567479621853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_2 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (21002055137847 / 25000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269922451641 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨2, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (21002055137847 / 25000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269922451641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_3 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (2624164001383 / 3125000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134963227103 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨3, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (2624164001383 / 3125000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134963227103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_4 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (20984575116371 / 25000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567482611539 / 25000000000000 : ℝ))
      (E := (cell12553 ⟨4, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (20984575116371 / 25000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567482611539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_5 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83903377778807 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134967218049 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨5, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83903377778807 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134967218049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_6 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (10483559993519 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134969216191 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨6, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (10483559993519 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134969216191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_7 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41916803468817 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269942443103 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨7, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41916803468817 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269942443103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_8 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41899379355779 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (22699464761 / 1000000000000 : ℝ))
      (E := (cell12553 ⟨8, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41899379355779 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (22699464761 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_9 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41881967617207 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567487605737 / 25000000000000 : ℝ))
      (E := (cell12553 ⟨9, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41881967617207 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567487605737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_10 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83729136470879 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (70936077029 / 3125000000000 : ℝ))
      (E := (cell12553 ⟨10, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83729136470879 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (70936077029 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_11 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (10461795298227 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134979217517 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨11, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (10461795298227 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134979217517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_12 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (8365961294427 / 10000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269962456109 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨12, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (8365961294427 / 10000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269962456109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_13 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83624888111469 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (283745802317 / 12500000000000 : ℝ))
      (E := (cell12553 ⟨13, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83624888111469 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (283745802317 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_14 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83590187852821 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269970444759 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨14, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83590187852821 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269970444759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_15 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41777756066957 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567493606143 / 25000000000000 : ℝ))
      (E := (cell12553 ⟨15, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41777756066957 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567493606143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_16 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41760430460259 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (453995684369 / 20000000000000 : ℝ))
      (E := (cell12553 ⟨16, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41760430460259 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (453995684369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_17 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83486234178577 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269982442107 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨17, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83486234178577 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2269982442107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_18 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83451631874213 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134993216213 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨18, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83451631874213 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134993216213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_19 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (83417053973723 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134995228007 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨19, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (83417053973723 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1134995228007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12554_0 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (84078225011839 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269786012513 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨0, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (84078225011839 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269786012513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_1 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (84043202864281 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269790020609 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨1, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (84043202864281 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269790020609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_2 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (84008205717729 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134897000417 / 50000000000000 : ℝ))
      (E := (cell12554 ⟨2, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (84008205717729 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134897000417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_3 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83973233535533 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269798020179 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨3, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83973233535533 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269798020179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_4 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83938286281239 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (283725253711 / 12500000000000 : ℝ))
      (E := (cell12554 ⟨4, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83938286281239 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (283725253711 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_5 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (41951681959291 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (226980603797 / 10000000000000 : ℝ))
      (E := (cell12554 ⟨5, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (41951681959291 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (226980603797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_6 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (2620889575359 / 3125000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134904997719 / 50000000000000 : ℝ))
      (E := (cell12554 ⟨6, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (2620889575359 / 3125000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134904997719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_7 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (20958398431019 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269814026033 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨7, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (20958398431019 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269814026033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_8 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83798745820649 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (22698180217 / 1000000000000 : ℝ))
      (E := (cell12554 ⟨8, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83798745820649 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (22698180217 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_9 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83763922665701 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269821989951 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨9, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83763922665701 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269821989951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_10 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (20932281055977 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269825996081 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨10, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (20932281055977 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269825996081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_11 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (16738870092027 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269829989117 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨11, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (16738870092027 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269829989117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_12 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83659601339427 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269833975819 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨12, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83659601339427 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269833975819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_13 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (20906219206753 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269838020801 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨13, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (20906219206753 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269838020801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_14 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83590176888301 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269842014149 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨14, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83590176888301 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269842014149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_15 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (20888875372221 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567461504989 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨15, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (20888875372221 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567461504989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_16 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (83520850594529 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (70932812057 / 3125000000000 : ℝ))
      (E := (cell12554 ⟨16, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (83520850594529 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (70932812057 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_17 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (41743112085591 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567463493851 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨17, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (41743112085591 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567463493851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_18 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (16690324436993 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (113492899699 / 5000000000000 : ℝ))
      (E := (cell12554 ⟨18, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (16690324436993 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (113492899699 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_19 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (41708522301089 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (45397239767 / 2000000000000 : ℝ))
      (E := (cell12554 ⟨19, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (41708522301089 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (45397239767 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12555_0 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (5254888095587 / 6250000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134828820589 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨0, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (5254888095587 / 6250000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134828820589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_1 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (84043187707653 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269661606757 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨1, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (84043187707653 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269661606757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_2 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (84008190886459 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269665603043 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨2, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (84008190886459 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269665603043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_3 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83973219029161 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (226966963923 / 10000000000000 : ℝ))
      (E := (cell12555 ⟨3, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83973219029161 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (226966963923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_4 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (10492284012413 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567418402119 / 25000000000000 : ℝ))
      (E := (cell12555 ⟨4, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (10492284012413 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567418402119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_5 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41951675030313 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269677635139 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨5, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41951675030313 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269677635139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_6 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (16773690575411 / 20000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134840805883 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨6, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (16773690575411 / 20000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134840805883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_7 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (20958395128177 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269685604341 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨7, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (20958395128177 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269685604341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_8 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (20949683232973 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269689620699 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨8, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (20949683232973 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269689620699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_9 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83763910099099 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269693610419 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨9, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83763910099099 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269693610419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_10 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83729111979009 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269697580763 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨10, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83729111979009 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269697580763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_11 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (16738867707297 / 20000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134850798397 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨11, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (16738867707297 / 20000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134850798397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_12 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (3346383589463 / 4000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (70928300227 / 3125000000000 : ℝ))
      (E := (cell12555 ⟨12, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (3346383589463 / 4000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (70928300227 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_13 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (83624865544509 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453941923737 / 20000000000000 : ℝ))
      (E := (cell12555 ⟨13, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (83624865544509 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453941923737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_14 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (1306096342589 / 1562500000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269713579199 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨14, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (1306096342589 / 1562500000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269713579199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_15 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (2611109088929 / 3125000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134858805521 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨15, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (2611109088929 / 3125000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134858805521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_16 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (668166722163 / 800000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567430400929 / 25000000000000 : ℝ))
      (E := (cell12555 ⟨16, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (668166722163 / 800000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567430400929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_17 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41743107082791 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269725620871 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨17, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41743107082791 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269725620871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_18 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (3338064499899 / 4000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567432402393 / 25000000000000 : ℝ))
      (E := (cell12555 ⟨18, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (3338064499899 / 4000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567432402393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_19 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (2606782351011 / 3125000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269733574787 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨19, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (2606782351011 / 3125000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269733574787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12556_0 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (16815638809883 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453905852987 / 20000000000000 : ℝ))
      (E := (cell12556 ⟨0, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (16815638809883 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453905852987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_1 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (16808634510691 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (70922913933 / 3125000000000 : ℝ))
      (E := (cell12556 ⟨1, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (16808634510691 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (70922913933 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_2 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (42004088028789 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269537258269 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨2, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (42004088028789 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269537258269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_3 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83973204525137 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134770626749 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨3, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83973204525137 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134770626749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_4 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41969128959839 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269545240409 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨4, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41969128959839 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269545240409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_5 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (4195166810247 / 5000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269549285517 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨5, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (4195166810247 / 5000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269549285517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_6 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83868439344851 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (226955328137 / 10000000000000 : ℝ))
      (E := (cell12556 ⟨6, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83868439344851 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (226955328137 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_7 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (8383356730353 / 10000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269557235987 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨7, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (8383356730353 / 10000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269557235987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_8 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (20949680011321 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134780636551 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨8, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (20949680011321 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134780636551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_9 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (5235243595913 / 6250000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567391306587 / 25000000000000 : ℝ))
      (E := (cell12556 ⟨9, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (5235243595913 / 6250000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567391306587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_10 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83729099736181 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453913855401 / 20000000000000 : ℝ))
      (E := (cell12556 ⟨10, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83729099736181 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453913855401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_11 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83694326614867 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453914651613 / 20000000000000 : ℝ))
      (E := (cell12556 ⟨11, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83694326614867 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453914651613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_12 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (20914894533929 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269577234291 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨12, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (20914894533929 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269577234291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_13 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41812427131979 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269581270293 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨13, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41812427131979 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269581270293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_14 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (20897538741251 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269585256159 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨14, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (20897538741251 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269585256159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_15 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83555480204447 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134794627989 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨15, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83555480204447 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134794627989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_16 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (10440103743507 / 12500000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269593217351 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨16, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (10440103743507 / 12500000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269593217351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_17 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83486204161779 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269597262121 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨17, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83486204161779 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269597262121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_18 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41725801405871 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269601220987 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨18, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41725801405871 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269601220987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_19 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (83417025864243 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (226960521533 / 10000000000000 : ℝ))
      (E := (cell12556 ⟨19, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (83417025864243 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (226960521533 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12557_0 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (84078178571907 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269400941581 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨0, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (84078178571907 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269400941581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_1 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (16808631480337 / 20000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (226940493791 / 10000000000000 : ℝ))
      (E := (cell12557 ⟨1, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (16808631480337 / 20000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (226940493791 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_2 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (42004080615543 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (141838060407 / 6250000000000 : ℝ))
      (E := (cell12557 ⟨2, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (42004080615543 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (141838060407 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_3 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41986595011731 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453882595743 / 20000000000000 : ℝ))
      (E := (cell12557 ⟨3, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41986595011731 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453882595743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_4 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83938243742361 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269416925489 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨4, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83938243742361 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269416925489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_5 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83903322351523 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134710465597 / 50000000000000 : ℝ))
      (E := (cell12557 ⟨5, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83903322351523 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134710465597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_6 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (20967106453719 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (283678118289 / 12500000000000 : ℝ))
      (E := (cell12557 ⟨6, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (20967106453719 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (283678118289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_7 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41916777048271 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567357230243 / 25000000000000 : ℝ))
      (E := (cell12557 ⟨7, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41916777048271 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567357230243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_8 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83798707160827 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567358230231 / 25000000000000 : ℝ))
      (E := (cell12557 ⟨8, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83798707160827 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567358230231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_9 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83763884972227 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1815549563 / 80000000000 : ℝ))
      (E := (cell12557 ⟨9, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83763884972227 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1815549563 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_10 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83729087495423 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (3546001423 / 156250000000 : ℝ))
      (E := (cell12557 ⟨10, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83729087495423 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (3546001423 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_11 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (1046178933691 / 1250000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269444914879 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨11, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (1046178933691 / 1250000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269444914879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_12 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83659566536849 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (70920278593 / 3125000000000 : ℝ))
      (E := (cell12557 ⟨12, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83659566536849 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (70920278593 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_13 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (1045310537317 / 1250000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567363229381 / 25000000000000 : ℝ))
      (E := (cell12557 ⟨13, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (1045310537317 / 1250000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567363229381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_14 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (3343605760249 / 4000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269456928783 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨14, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (3343605760249 / 4000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269456928783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_15 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83555469565039 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453892190953 / 20000000000000 : ℝ))
      (E := (cell12557 ⟨15, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83555469565039 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453892190953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_16 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83520819627571 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (70920779471 / 3125000000000 : ℝ))
      (E := (cell12557 ⟨16, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83520819627571 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (70920779471 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_17 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (83486194159771 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567367224789 / 25000000000000 : ℝ))
      (E := (cell12557 ⟨17, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (83486194159771 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (567367224789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_18 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (20862898281941 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134736472331 / 50000000000000 : ℝ))
      (E := (cell12557 ⟨18, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (20862898281941 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134736472331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_19 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (20854254124463 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269476909977 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨19, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (20854254124463 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269476909977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12558_0 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (42039081548433 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269272671119 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨0, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (42039081548433 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269272671119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_1 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (10505392781543 / 12500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269276682919 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨1, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (10505392781543 / 12500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269276682919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_2 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (42004073203491 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134640334967 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨2, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (42004073203491 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134640334967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_3 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (16794635104827 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (45385693983 / 2000000000000 : ℝ))
      (E := (cell12558 ⟨3, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (16794635104827 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (45385693983 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_4 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83938229567353 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134644331859 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨4, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83938229567353 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134644331859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_5 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41951654250187 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134646343999 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨5, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41951654250187 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134646343999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_6 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (8386841228713 / 10000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567324166133 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨6, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (8386841228713 / 10000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567324166133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_7 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41916770445871 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (22693006593 / 1000000000000 : ℝ))
      (E := (cell12558 ⟨7, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41916770445871 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (22693006593 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_8 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41899347139259 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269304680137 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨8, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41899347139259 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269304680137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_9 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (16752774482391 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269308676617 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨9, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (16752774482391 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269308676617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_10 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (16745815051347 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269312655999 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨10, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (16745815051347 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269312655999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_11 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (20923575694431 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (141832292709 / 6250000000000 : ℝ))
      (E := (cell12558 ⟨11, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (20923575694431 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (141832292709 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_12 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (20914888734993 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134660324663 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨12, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (20914888734993 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134660324663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_13 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83624831708713 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269324676581 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨13, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83624831708713 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269324676581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_14 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83590133049359 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567332163799 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨14, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83590133049359 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567332163799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_15 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (5222216182969 / 6250000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269332649259 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨15, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (5222216182969 / 6250000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269332649259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_16 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (2088020232723 / 2500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269336664539 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨16, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (2088020232723 / 2500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269336664539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_17 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83486184159557 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134670324183 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨17, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83486184159557 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134670324183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_18 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41725791722771 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567336166041 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨18, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41725791722771 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567336166041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_19 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (83417007133177 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567337164683 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨19, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (83417007133177 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567337164683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12559_0 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (42039073812147 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134572226773 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨0, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (42039073812147 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134572226773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_1 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (8404312710543 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269148480883 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨1, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (8404312710543 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269148480883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_2 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (16801626317053 / 20000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134576242109 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨2, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (16801626317053 / 20000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134576242109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_3 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20993290256789 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269156472669 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨3, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20993290256789 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269156472669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_4 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20984553848663 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (453832091019 / 20000000000000 : ℝ))
      (E := (cell12559 ⟨4, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20984553848663 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (453832091019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_5 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83903294651493 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269164440101 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨5, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83903294651493 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269164440101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_6 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20967099690403 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269168436029 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨6, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20967099690403 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269168436029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_7 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (8383352768913 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269172450969 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨7, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (8383352768913 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269172450969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_8 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41899340699179 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269176434771 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨8, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41899340699179 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269176434771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_9 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83763859853793 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (283647556619 / 12500000000000 : ℝ))
      (E := (cell12559 ⟨9, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83763859853793 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (283647556619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_10 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20932265755029 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567296113703 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨10, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20932265755029 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567296113703 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_11 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83694290862197 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269188447353 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨11, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83694290862197 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269188447353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_12 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83659543345087 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134596218667 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨12, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83659543345087 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134596218667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_13 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83624820434017 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (70912388477 / 3125000000000 : ℝ))
      (E := (cell12559 ⟨13, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83624820434017 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (70912388477 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_14 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20897530523601 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269200435399 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨14, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20897530523601 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269200435399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_15 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (83555448291841 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269204455753 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨15, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (83555448291841 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269204455753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_16 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41760399496051 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269208439923 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨16, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41760399496051 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269208439923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_17 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41743087080569 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134606225777 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨17, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41743087080569 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134606225777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_18 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20862893441269 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269216437709 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨18, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20862893441269 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269216437709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_19 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41708498885109 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (453844092319 / 20000000000000 : ℝ))
      (E := (cell12559 ⟨19, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41708498885109 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (453844092319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12560_0 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (21019533038547 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269016288869 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨0, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (21019533038547 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269016288869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_1 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (42021555980471 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567255068497 / 25000000000000 : ℝ))
      (E := (cell12560 ⟨1, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (42021555980471 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567255068497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_2 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (5250507297871 / 6250000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134512146841 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨2, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (5250507297871 / 6250000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134512146841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_3 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (20993286633131 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (90761131971 / 4000000000000 : ℝ))
      (E := (cell12560 ⟨3, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (20993286633131 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (90761131971 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_4 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41969100612129 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (18152258397 / 800000000000 : ℝ))
      (E := (cell12560 ⟨4, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41969100612129 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (18152258397 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_5 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83903280804879 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269036303333 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨5, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83903280804879 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269036303333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_6 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83868385238321 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269040260807 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨6, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83868385238321 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269040260807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_7 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83833514488707 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134522147991 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨7, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83833514488707 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134522147991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_8 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41899334260173 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134524150399 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨8, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41899334260173 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134524150399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_9 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83763847297739 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269052282761 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨9, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83763847297739 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269052282761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_10 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83729050785567 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (226905624913 / 10000000000000 : ℝ))
      (E := (cell12560 ⟨10, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83729050785567 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (226905624913 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_11 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (836942789487 / 1000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567265066241 / 25000000000000 : ℝ))
      (E := (cell12560 ⟨11, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (836942789487 / 1000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567265066241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_12 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83659531752191 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269064279009 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨12, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83659531752191 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269064279009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_13 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (10453101145159 / 12500000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134534119837 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨13, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (10453101145159 / 12500000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134534119837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_14 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83590111141361 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269072269393 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨14, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83590111141361 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269072269393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_15 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83555437658051 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453815251591 / 20000000000000 : ℝ))
      (E := (cell12560 ⟨15, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83555437658051 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453815251591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_16 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41760394338559 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134540134613 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨16, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41760394338559 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134540134613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_17 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (83486164164513 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567271062633 / 25000000000000 : ℝ))
      (E := (cell12560 ⟨17, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (83486164164513 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (567271062633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_18 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (20862891021591 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269088265301 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨18, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (20862891021591 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269088265301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_19 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (5213561775561 / 6250000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (90763690413 / 4000000000000 : ℝ))
      (E := (cell12560 ⟨19, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (5213561775561 / 6250000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (90763690413 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12561_0 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (84078116686549 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (453777635417 / 20000000000000 : ℝ))
      (E := (cell12561 ⟨0, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (84078116686549 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (453777635417 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_1 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (42021548409441 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226889217787 / 10000000000000 : ℝ))
      (E := (cell12561 ⟨1, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (42021548409441 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226889217787 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_2 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (1312626592953 / 1562500000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268896156171 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨2, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (1312626592953 / 1562500000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268896156171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_3 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41986566020119 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (141806257569 / 6250000000000 : ℝ))
      (E := (cell12561 ⟨3, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41986566020119 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (141806257569 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_4 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (8393818705617 / 10000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134452069709 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨4, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (8393818705617 / 10000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134452069709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_5 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (20975816740133 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268908161869 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨5, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (20975816740133 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268908161869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_6 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (83868371717257 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (453782427773 / 20000000000000 : ℝ))
      (E := (cell12561 ⟨6, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (83868371717257 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (453782427773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_7 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (8383350129047 / 10000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268916136381 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨7, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (8383350129047 / 10000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268916136381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_8 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41899327822241 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (9075680649 / 400000000000 : ℝ))
      (E := (cell12561 ⟨8, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41899327822241 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (9075680649 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_9 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (5235239671487 / 6250000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268924108037 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨9, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (5235239671487 / 6250000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268924108037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_10 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41864519276543 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268928155017 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨10, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41864519276543 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268928155017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_11 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (5230891689827 / 6250000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (90757285447 / 4000000000000 : ℝ))
      (E := (cell12561 ⟨11, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (5230891689827 / 6250000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (90757285447 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_12 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (16731904032257 / 20000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268936116271 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨12, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (16731904032257 / 20000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268936116271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_13 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41812398945239 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567235025453 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨13, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41812398945239 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567235025453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_14 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (20897525047557 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268944099057 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨14, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (20897525047557 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268944099057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_15 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (83555427026133 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268948114013 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨15, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (83555427026133 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268948114013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_16 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41760389181983 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134476047139 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨16, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41760389181983 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134476047139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_17 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (83486154169681 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134478051747 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨17, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (83486154169681 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134478051747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_18 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (83451554409407 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268960146939 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨18, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (83451554409407 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268960146939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_19 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (10427122381181 / 12500000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268964113167 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨19, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (10427122381181 / 12500000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2268964113167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12562_0 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (672624809771 / 800000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134380030201 / 50000000000000 : ℝ))
      (E := (cell12562 ⟨0, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (672624809771 / 800000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134380030201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_1 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (84043081679247 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134382038447 / 50000000000000 : ℝ))
      (E := (cell12562 ⟨1, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (84043081679247 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134382038447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_2 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (16801617426887 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268768071683 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨2, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (16801617426887 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268768071683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_3 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41986558775149 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268772053887 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨3, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41986558775149 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268772053887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_4 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83938172890389 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268776032363 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨4, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83938172890389 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268776032363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_5 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83903253118451 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268780073623 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨5, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83903253118451 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268780073623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_6 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (4193417909921 / 5000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134392035103 / 50000000000000 : ℝ))
      (E := (cell12562 ⟨6, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (4193417909921 / 5000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134392035103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_7 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (4191674404721 / 5000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268788030127 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨7, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (4191674404721 / 5000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268788030127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_8 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (16759728554153 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268792019129 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨8, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (16759728554153 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268792019129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_9 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41881911095977 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268796044793 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨9, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41881911095977 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268796044793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_10 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83729026322673 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268800056411 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨10, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83729026322673 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268800056411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_11 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83694255127793 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567201015247 / 25000000000000 : ℝ))
      (E := (cell12562 ⟨11, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83694255127793 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567201015247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_12 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83659508572367 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268808065277 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨12, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83659508572367 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268808065277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_13 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83624786621633 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268812017681 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨13, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83624786621633 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268812017681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_14 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83590089241007 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268816040637 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨14, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83590089241007 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268816040637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_15 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41777708198043 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283602502991 / 12500000000000 : ℝ))
      (E := (cell12562 ⟨15, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41777708198043 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283602502991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_16 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (83520768052647 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (113441201571 / 5000000000000 : ℝ))
      (E := (cell12562 ⟨16, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (83520768052647 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (113441201571 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_17 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41743072088321 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (56720700261 / 2500000000000 : ℝ))
      (E := (cell12562 ⟨17, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41743072088321 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (56720700261 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_18 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (20862886183551 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283604003051 / 12500000000000 : ℝ))
      (E := (cell12562 ⟨18, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (20862886183551 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283604003051 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_19 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (20854242422909 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268836020119 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨19, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (20854242422909 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268836020119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12563_0 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (84078085758667 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (453726399323 / 20000000000000 : ℝ))
      (E := (cell12563 ⟨0, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (84078085758667 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (453726399323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_1 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (84043066542037 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268636028879 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨1, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (84043066542037 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268636028879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_2 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (42004036161131 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (113431999119 / 5000000000000 : ℝ))
      (E := (cell12563 ⟨2, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (42004036161131 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (113431999119 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_3 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83973103062703 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (283580497737 / 12500000000000 : ℝ))
      (E := (cell12563 ⟨3, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83973103062703 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (283580497737 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_4 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (327883432527 / 390625000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (70895249327 / 3125000000000 : ℝ))
      (E := (cell12563 ⟨4, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (327883432527 / 390625000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (70895249327 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_5 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (16780647855727 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268651980683 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨5, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (16780647855727 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268651980683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_6 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (5241771542613 / 6250000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268655996893 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨6, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (5241771542613 / 6250000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268655996893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_7 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83833474900557 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134329988609 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨7, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83833474900557 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134329988609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_8 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41899314949597 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567165996851 / 25000000000000 : ℝ))
      (E := (cell12563 ⟨8, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41899314949597 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567165996851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_9 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41881904821111 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134333988509 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨9, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41881904821111 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134333988509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_10 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83729014094327 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (453734402269 / 20000000000000 : ℝ))
      (E := (cell12563 ⟨10, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83729014094327 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (453734402269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_11 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83694243220381 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268675981351 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨11, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83694243220381 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268675981351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_12 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83659496985439 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (141792500617 / 6250000000000 : ℝ))
      (E := (cell12563 ⟨12, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83659496985439 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (141792500617 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_13 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83624775354737 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134341993641 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨13, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83624775354737 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134341993641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_14 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (16718015658739 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (70896499309 / 3125000000000 : ℝ))
      (E := (cell12563 ⟨14, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (16718015658739 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (70896499309 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_15 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (83555405767909 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268691987703 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨15, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (83555405767909 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268691987703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_16 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41760378871579 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567173991079 / 25000000000000 : ℝ))
      (E := (cell12563 ⟨16, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41760378871579 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567173991079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_17 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (20871533546349 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268699971371 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨17, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (20871533546349 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268699971371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_18 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41725767530377 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134351977963 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨18, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41725767530377 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134351977963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_19 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41708480167769 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (453741596237 / 20000000000000 : ℝ))
      (E := (cell12563 ⟨19, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41708480167769 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (453741596237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12564_0 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (84078070298423 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268503985729 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨0, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (84078070298423 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268503985729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_1 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (21010762851813 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (567127008457 / 25000000000000 : ℝ))
      (E := (cell12564 ⟨1, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (21010762851813 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (567127008457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_2 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (3360322300499 / 4000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134256001973 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨2, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (3360322300499 / 4000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134256001973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_3 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83973088577453 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268516020863 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨3, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83973088577453 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268516020863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_4 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83938144565741 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134259988861 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨4, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83938144565741 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134259988861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_5 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (16780645088217 / 20000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134261999439 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨5, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (16780645088217 / 20000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134261999439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_6 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41934165583711 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134263988433 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨6, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41934165583711 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134263988433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_7 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41916730854439 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268531977661 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨7, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41916730854439 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268531977661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_8 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (8379861702977 / 10000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (567134002273 / 25000000000000 : ℝ))
      (E := (cell12564 ⟨8, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (8379861702977 / 10000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (567134002273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_9 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83763797094597 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268539962721 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨9, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83763797094597 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268539962721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_10 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83729001868049 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (226854396179 / 10000000000000 : ℝ))
      (E := (cell12564 ⟨10, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83729001868049 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (226854396179 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_11 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83694231314997 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134274006687 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨11, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83694231314997 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134274006687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_12 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83659485400499 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268552008137 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨12, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83659485400499 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268552008137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_13 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83624764089791 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134277976257 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨13, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83624764089791 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134277976257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_14 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (20897516837073 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134279984469 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨14, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (20897516837073 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134279984469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_15 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83555395141603 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134282002669 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨15, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83555395141603 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134282002669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_16 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41760373717751 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134283975567 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨16, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41760373717751 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134283975567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_17 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41743062097971 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268571986291 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨17, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41743062097971 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268571986291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_18 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (83451525389057 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134287999857 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨18, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (83451525389057 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134287999857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_19 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41708475490577 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (453715999273 / 20000000000000 : ℝ))
      (E := (cell12564 ⟨19, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41708475490577 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (453715999273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12565_0 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (21019513710161 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134188013871 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨0, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (21019513710161 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134188013871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_1 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (84043036274891 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134190016961 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨1, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (84043036274891 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134190016961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_2 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (84008042705071 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268384020701 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨2, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (84008042705071 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268384020701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_3 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83973074094547 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134194027529 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨3, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83973074094547 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134194027529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_4 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41969065203437 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268392030139 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨4, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41969065203437 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268392030139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_5 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83903211605799 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268396012381 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨5, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83903211605799 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268396012381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_6 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (4193415882763 / 5000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134200005063 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨6, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (4193415882763 / 5000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134200005063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_7 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (16766689703877 / 20000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (453680806291 / 20000000000000 : ℝ))
      (E := (cell12565 ⟨7, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (16766689703877 / 20000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (453680806291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_8 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (8379860416249 / 10000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567102006553 / 25000000000000 : ℝ))
      (E := (cell12565 ⟨8, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (8379860416249 / 10000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567102006553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_9 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41881892274539 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134206000951 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨9, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41881892274539 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134206000951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_10 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83728989643837 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268416023809 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨10, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83728989643837 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268416023809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_11 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (2092355485291 / 2500000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (45368400819 / 2000000000000 : ℝ))
      (E := (cell12565 ⟨11, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (2092355485291 / 2500000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (45368400819 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_12 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41829736908773 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567106000499 / 25000000000000 : ℝ))
      (E := (cell12565 ⟨12, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41829736908773 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567106000499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_13 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (10453094103349 / 12500000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268428029583 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨13, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (10453094103349 / 12500000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268428029583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_14 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83590056404799 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (453686402757 / 20000000000000 : ℝ))
      (E := (cell12565 ⟨14, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83590056404799 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (453686402757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_15 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83555384517167 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268436018687 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨15, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83555384517167 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268436018687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_16 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (3340829485187 / 4000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (56710999797 / 2500000000000 : ℝ))
      (E := (cell12565 ⟨16, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (3340829485187 / 4000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (56710999797 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_17 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (2087152855207 / 2500000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567110999251 / 25000000000000 : ℝ))
      (E := (cell12565 ⟨17, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (2087152855207 / 2500000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567110999251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_18 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (83451515719113 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (453689607867 / 20000000000000 : ℝ))
      (E := (cell12565 ⟨18, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (83451515719113 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (453689607867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_19 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (20854235407121 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (113422600371 / 5000000000000 : ℝ))
      (E := (cell12565 ⟨19, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (20854235407121 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (113422600371 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12566_0 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (5254877461583 / 6250000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268248122657 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨0, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (5254877461583 / 6250000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268248122657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_1 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (84043021144953 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134126072401 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨1, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (84043021144953 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134126072401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_2 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (84008027900051 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (283532018541 / 12500000000000 : ℝ))
      (E := (cell12566 ⟨2, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (84008027900051 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (283532018541 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_3 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (16794611922797 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268260142347 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨3, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (16794611922797 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268260142347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_4 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83938116250311 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268264135713 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨4, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83938116250311 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268264135713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_5 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83903197772777 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268268137021 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨5, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83903197772777 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268268137021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_6 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83868304145323 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (70883503021 / 3125000000000 : ℝ))
      (E := (cell12566 ⟨6, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83868304145323 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (70883503021 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_7 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83833435332077 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134138069299 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨7, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83833435332077 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134138069299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_8 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20949647824339 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134140048373 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨8, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20949647824339 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134140048373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_9 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (2617617875177 / 3125000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268284094563 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨9, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (2617617875177 / 3125000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268284094563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_10 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (8372897742169 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268288081341 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨10, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (8372897742169 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268288081341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_11 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (8369420751031 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567073030533 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨11, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (8369420751031 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567073030533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_12 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (4182973111829 / 5000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268296107603 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨12, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (4182973111829 / 5000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268296107603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_13 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83624741565741 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567075025571 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨13, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83624741565741 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567075025571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_14 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (41795022731607 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (226830411243 / 10000000000000 : ℝ))
      (E := (cell12566 ⟨14, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (41795022731607 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (226830411243 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_15 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83555373894601 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268308085897 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨15, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83555373894601 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268308085897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_16 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83520726825679 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268312086549 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨16, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83520726825679 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268312086549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_17 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (10435763027801 / 12500000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134158059951 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨17, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (10435763027801 / 12500000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134158059951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_18 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83451506050921 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268320074791 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨18, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83451506050921 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268320074791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_19 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (83416932277527 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (226832407259 / 10000000000000 : ℝ))
      (E := (cell12566 ⟨19, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (83416932277527 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (226832407259 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12567_0 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (3363120957299 / 4000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567030067619 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨0, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (3363120957299 / 4000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567030067619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_1 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (42021503008719 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (226812425083 / 10000000000000 : ℝ))
      (E := (cell12567 ⟨1, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (42021503008719 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (226812425083 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_2 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (42004006548707 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (283516033893 / 12500000000000 : ℝ))
      (E := (cell12567 ⟨2, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (42004006548707 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (283516033893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_3 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (16794609027153 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268132224867 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨3, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (16794609027153 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268132224867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_4 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83938102096051 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268136236559 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨4, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83938102096051 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268136236559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_5 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83903183942019 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268140256973 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨5, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83903183942019 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268140256973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_6 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83868290637609 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268144236509 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨6, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83868290637609 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268144236509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_7 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83833422146953 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (141759265071 / 6250000000000 : ℝ))
      (E := (cell12567 ⟨7, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83833422146953 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (141759265071 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_8 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41899289217183 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268152220699 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨8, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41899289217183 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268152220699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_9 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (16752751892871 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268156240707 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨9, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (16752751892871 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268156240707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_10 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (8372896520161 / 10000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (141760015653 / 6250000000000 : ℝ))
      (E := (cell12567 ⟨10, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (8372896520161 / 10000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (141760015653 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_11 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (16738839122201 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (90726570277 / 4000000000000 : ℝ))
      (E := (cell12567 ⟨11, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (16738839122201 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (90726570277 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_12 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83659450657601 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134084104403 / 50000000000000 : ℝ))
      (E := (cell12567 ⟨12, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83659450657601 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134084104403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_13 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41812365153319 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268172228723 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨13, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41812365153319 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268172228723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_14 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41795017261769 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268176206751 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨14, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41795017261769 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268176206751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_15 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83555363273903 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268180206973 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨15, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83555363273903 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268180206973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_16 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83520716523513 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567046058787 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨16, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83520716523513 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567046058787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_17 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (10435761779791 / 12500000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567047059649 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨17, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (10435761779791 / 12500000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567047059649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_18 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83451496384481 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268192222521 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨18, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83451496384481 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268192222521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_19 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (83416922928283 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268196191879 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨19, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (83416922928283 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268196191879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12568_0 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (21019502120521 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1133996206701 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨0, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (21019502120521 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1133996206701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_1 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (16808598178469 / 20000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (566999102457 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨1, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (16808598178469 / 20000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (566999102457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_2 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (84007998297159 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268000389151 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨2, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (84007998297159 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268000389151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_3 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (5248314416243 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268004418351 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨3, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (5248314416243 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268004418351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_4 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83938087944093 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283501048821 / 12500000000000 : ℝ))
      (E := (cell12568 ⟨4, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83938087944093 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283501048821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_5 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83903170113523 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283501553769 / 12500000000000 : ℝ))
      (E := (cell12568 ⟨5, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83903170113523 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283501553769 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_6 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83868277132119 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567004107409 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨6, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83868277132119 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567004107409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_7 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (20958352241003 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268020397029 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨7, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (20958352241003 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268020397029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_8 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (1047482069669 / 1250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268024398071 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨8, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (1047482069669 / 1250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268024398071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_9 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (1675274938503 / 2000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (90721135293 / 4000000000000 : ℝ))
      (E := (cell12568 ⟨9, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (1675274938503 / 2000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (90721135293 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_10 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (41864476491797 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (70876012971 / 3125000000000 : ℝ))
      (E := (cell12568 ⟨10, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (41864476491797 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (70876012971 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_11 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (41847091856863 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134018193637 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨11, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (41847091856863 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134018193637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_12 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (2614357471269 / 3125000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268040421761 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨12, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (2614357471269 / 3125000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268040421761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_13 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83624719049481 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268044408901 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨13, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83624719049481 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268044408901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_14 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83590023585769 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268048412999 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨14, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83590023585769 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268048412999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_15 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83555352655073 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134026190957 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨15, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83555352655073 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134026190957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_16 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (10440088277897 / 12500000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (141753523719 / 6250000000000 : ℝ))
      (E := (cell12568 ⟨16, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (10440088277897 / 12500000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (141753523719 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_17 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83486084256037 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567015102821 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨17, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83486084256037 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567015102821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_18 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (5215717919987 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283508045761 / 12500000000000 : ℝ))
      (E := (cell12568 ⟨18, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (5215717919987 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283508045761 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_19 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (83416913580751 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283508545661 / 12500000000000 : ℝ))
      (E := (cell12568 ⟨19, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (83416913580751 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283508545661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12569_0 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (16815598606831 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453572921847 / 20000000000000 : ℝ))
      (E := (cell12569 ⟨0, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (16815598606831 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453572921847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_1 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (3361719030787 / 4000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453573724359 / 20000000000000 : ℝ))
      (E := (cell12569 ⟨1, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (3361719030787 / 4000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453573724359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_2 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (16801596699857 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (566968154509 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨2, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (16801596699857 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (566968154509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_3 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83973016186353 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (566969151767 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨3, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83973016186353 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (566969151767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_4 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41969036897219 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267880597739 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨4, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41969036897219 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267880597739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_5 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83903156287289 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453576919729 / 20000000000000 : ℝ))
      (E := (cell12569 ⟨5, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83903156287289 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453576919729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_6 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83868263628851 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267888618117 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨6, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83868263628851 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267888618117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_7 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41916697891627 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267892606277 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨7, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41916697891627 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267892606277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_8 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41899276357409 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133948314431 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨8, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41899276357409 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133948314431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_9 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (1675274687761 / 2000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133950317717 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨9, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (1675274687761 / 2000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133950317717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_10 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41864470383821 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453580926649 / 20000000000000 : ℝ))
      (E := (cell12569 ⟨10, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41864470383821 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453580926649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_11 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (10461771477309 / 12500000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (283488578661 / 12500000000000 : ℝ))
      (E := (cell12569 ⟨11, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (10461771477309 / 12500000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (283488578661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_12 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83659427505601 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267912630313 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨12, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83659427505601 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267912630313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_13 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83624707794271 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (566979146179 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨13, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83624707794271 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (566979146179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_14 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83590012649907 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133960307463 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨14, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83590012649907 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1133960307463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_15 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (2611104438691 / 3125000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267924610721 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨15, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (2611104438691 / 3125000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267924610721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_16 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (20880173981167 / 25000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226792857779 / 10000000000000 : ℝ))
      (E := (cell12569 ⟨16, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (20880173981167 / 25000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226792857779 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_17 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83486074275537 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267932579769 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨17, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83486074275537 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267932579769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_18 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41725738528427 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226793662193 / 10000000000000 : ℝ))
      (E := (cell12569 ⟨18, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41725738528427 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (226793662193 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_19 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (83416904234931 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267940592817 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨19, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (83416904234931 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2267940592817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12570_0 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (84077977588687 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267736915771 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨0, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (84077977588687 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267736915771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_1 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (3361718425977 / 4000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133870443367 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨1, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (3361718425977 / 4000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133870443367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_2 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (84007968703793 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267744899957 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨2, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (84007968703793 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267744899957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_3 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (2099325042879 / 2500000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267748906751 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨3, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (2099325042879 / 2500000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267748906751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_4 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (20984514911771 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (90710114323 / 4000000000000 : ℝ))
      (E := (cell12570 ⟨4, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (20984514911771 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (90710114323 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_5 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41951571231659 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267756878279 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨5, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41951571231659 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267756878279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_6 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (16773650025561 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566940214973 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨6, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (16773650025561 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566940214973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_7 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41916691302339 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267764868883 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨7, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41916691302339 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267764868883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_8 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41899269929129 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226776885509 / 10000000000000 : ℝ))
      (E := (cell12570 ⟨8, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41899269929129 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226776885509 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_9 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (20940930463263 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133886442011 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨9, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (20940930463263 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133886442011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_10 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41864464276877 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133888423467 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨10, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41864464276877 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133888423467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_11 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (83694159925243 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267780866861 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨11, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (83694159925243 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267780866861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_12 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (83659415932579 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (70868276077 / 3125000000000 : ℝ))
      (E := (cell12570 ⟨12, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (83659415932579 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (70868276077 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_13 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (83624696541007 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566947218093 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨13, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (83624696541007 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566947218093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_14 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (5224375107247 / 6250000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (8858565901 / 390625000000 : ℝ))
      (E := (cell12570 ⟨14, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (5224375107247 / 6250000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (8858565901 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_15 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41777665711509 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (141737302203 / 6250000000000 : ℝ))
      (E := (cell12570 ⟨15, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41777665711509 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (141737302203 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_16 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (83520685627989 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133900415003 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨16, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (83520685627989 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133900415003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_17 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41743032148413 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566951215111 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨17, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41743032148413 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566951215111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_18 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41725733697833 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566952218403 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨18, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41725733697833 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566952218403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_19 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41708447445411 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566953218617 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨19, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41708447445411 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566953218617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12571_0 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (84077962145679 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267609159623 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨0, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (84077962145679 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267609159623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_1 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (21010736382899 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267613204647 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨1, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (21010736382899 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267613204647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_2 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (42003976955341 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (141726073567 / 6250000000000 : ℝ))
      (E := (cell12571 ⟨2, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (42003976955341 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (141726073567 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_3 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83972987246307 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267621201669 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨3, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83972987246307 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267621201669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_4 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83938045502031 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133812585789 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨4, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83938045502031 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133812585789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_5 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83903128641607 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267629153231 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨5, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83903128641607 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267629153231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_6 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83868236628981 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267633154961 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨6, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83868236628981 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267633154961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_7 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (16766673885657 / 20000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133818592423 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨7, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (16766673885657 / 20000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133818592423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_8 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83798527003841 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (90705647709 / 4000000000000 : ℝ))
      (E := (cell12571 ⟨8, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83798527003841 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (90705647709 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_9 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41881854660079 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (141727824131 / 6250000000000 : ℝ))
      (E := (cell12571 ⟨9, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41881854660079 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (141727824131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_10 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (8372891634193 / 10000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (453529834441 / 20000000000000 : ℝ))
      (E := (cell12571 ⟨10, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (8372891634193 / 10000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (453529834441 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_11 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83694148034037 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267653158049 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨11, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83694148034037 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267653158049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_12 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41829702180771 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267657150371 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨12, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41829702180771 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267657150371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_13 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (10453085661211 / 12500000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (226766115567 / 10000000000000 : ℝ))
      (E := (cell12571 ⟨13, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (10453085661211 / 12500000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (226766115567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_14 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83589990783903 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (70864536881 / 3125000000000 : ℝ))
      (E := (cell12571 ⟨14, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83589990783903 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (70864536881 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_15 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83555320809791 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (141729323237 / 6250000000000 : ℝ))
      (E := (cell12571 ⟨15, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83555320809791 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (141729323237 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_16 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83520675333137 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267673136157 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨16, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83520675333137 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267673136157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_17 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (83486054319903 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267677136921 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨17, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (83486054319903 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267677136921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_18 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (20862864434057 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133840589677 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨18, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (20862864434057 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133840589677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_19 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (3336675421937 / 4000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133842575999 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨19, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (3336675421937 / 4000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133842575999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12572_0 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (21019486676283 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133740757091 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨0, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (21019486676283 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133740757091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_1 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (42021465208093 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453497103543 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨1, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (42021465208093 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453497103543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_2 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (84007939119951 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133744753613 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨2, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (84007939119951 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133744753613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_3 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41986486389897 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (90699739673 / 4000000000000 : ℝ))
      (E := (cell12572 ⟨3, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41986486389897 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (90699739673 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_4 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41969015679639 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267497538249 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨4, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41969015679639 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267497538249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_5 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41951557411079 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (553589243 / 24414062500 : ℝ))
      (E := (cell12572 ⟨5, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41951557411079 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (553589243 / 24414062500 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_6 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41934111566189 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133752751663 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨6, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41934111566189 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133752751663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_7 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (10479169531759 / 12500000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267509496211 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨7, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (10479169531759 / 12500000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267509496211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_8 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (16759702830313 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267513525801 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨8, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (16759702830313 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267513525801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_9 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (16752739357873 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267517483651 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨9, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (16752739357873 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267517483651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_10 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83728904132169 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267521492997 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨10, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83728904132169 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267521492997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_11 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (16738827228971 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267525502853 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨11, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (16738827228971 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267525502853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_12 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83659392792489 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133764759979 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨12, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83659392792489 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133764759979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_13 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41812337020157 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267533492711 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨13, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41812337020157 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267533492711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_14 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (261218687043 / 312500000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (226753748541 / 10000000000000 : ℝ))
      (E := (cell12572 ⟨14, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (261218687043 / 312500000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (226753748541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_15 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83555310198431 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267541504059 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨15, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83555310198431 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267541504059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_16 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (83520665040113 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267545496241 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨16, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (83520665040113 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267545496241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_17 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (8348604434477 / 10000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453509893479 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨17, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (8348604434477 / 10000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453509893479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_18 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (4172572403927 / 5000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267553480939 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨18, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (4172572403927 / 5000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267553480939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_19 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41708438103869 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453511496731 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨19, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41708438103869 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453511496731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12573_0 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (21019482816761 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267353921653 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨0, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (21019482816761 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267353921653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_1 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (84042915303197 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267357883757 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨1, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (84042915303197 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267357883757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_2 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (84007924331599 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267361890421 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨2, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (84007924331599 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267361890421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_3 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83972958315621 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (283420736619 / 12500000000000 : ℝ))
      (E := (cell12573 ⟨3, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83972958315621 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (283420736619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_4 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (3357520688753 / 4000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133684950099 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨4, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (3357520688753 / 4000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133684950099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_5 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (10487887625621 / 12500000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (453474784149 / 20000000000000 : ℝ))
      (E := (cell12573 ⟨5, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (10487887625621 / 12500000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (453474784149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_6 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (16773641927599 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267377904989 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨6, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (16773641927599 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267377904989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_7 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83833343082041 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (141711369931 / 6250000000000 : ℝ))
      (E := (cell12573 ⟨7, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83833343082041 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (141711369931 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_8 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83798501301431 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267385912301 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨8, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83798501301431 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267385912301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_9 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (3350547370427 / 4000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133694946351 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨9, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (3350547370427 / 4000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133694946351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_10 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (8372889192447 / 10000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267393867343 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨10, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (8372889192447 / 10000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267393867343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_11 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (2615441383053 / 3125000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267397901273 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨11, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (2615441383053 / 3125000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267397901273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_12 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83659381225419 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267401885149 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨12, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83659381225419 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267401885149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_13 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (16724932558577 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (283425735437 / 12500000000000 : ℝ))
      (E := (cell12573 ⟨13, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (16724932558577 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (283425735437 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_14 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (41794984462761 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267409902561 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨14, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (41794984462761 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267409902561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_15 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83555299588937 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267413890197 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨15, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83555299588937 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267413890197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_16 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (20880163687229 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (283427231511 / 12500000000000 : ℝ))
      (E := (cell12573 ⟨16, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (20880163687229 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (283427231511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_17 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (2608938574107 / 3125000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566855462967 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨17, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (2608938574107 / 3125000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566855462967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_18 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83451438422601 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566856473701 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨18, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83451438422601 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566856473701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_19 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (83416866868761 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566857467359 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨19, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (83416866868761 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566857467359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12574_0 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (42038957915707 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (28340329053 / 1250000000000 : ℝ))
      (E := (cell12574 ⟨0, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (42038957915707 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (28340329053 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_1 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (42021450096313 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133615151389 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨1, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (42021450096313 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133615151389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_2 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (42003954772813 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133617163329 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨2, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (42003954772813 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133617163329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_3 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83972943853787 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (453447669437 / 20000000000000 : ℝ))
      (E := (cell12574 ⟨3, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83972943853787 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (453447669437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_4 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (2623062596271 / 3125000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267242315317 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨4, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (2623062596271 / 3125000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267242315317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_5 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41951543595019 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267246297483 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨5, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41951543595019 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267246297483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_6 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (10483524518229 / 12500000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133625151007 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨6, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (10483524518229 / 12500000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133625151007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_7 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (8383332991219 / 10000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (283406792123 / 12500000000000 : ℝ))
      (E := (cell12574 ⟨7, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (8383332991219 / 10000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (283406792123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_8 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83798488453437 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (453451658849 / 20000000000000 : ℝ))
      (E := (cell12574 ⟨8, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83798488453437 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (453451658849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_9 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41881835867043 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267262297237 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨9, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41881835867043 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267262297237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_10 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (5233054982427 / 6250000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566816573811 / 25000000000000 : ℝ))
      (E := (cell12574 ⟨10, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (5233054982427 / 6250000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566816573811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_11 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (1046176404657 / 1250000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267270295257 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨11, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (1046176404657 / 1250000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267270295257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_12 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83659369660333 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267274304021 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨12, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83659369660333 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267274304021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_13 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (83624651547399 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566819582007 / 25000000000000 : ℝ))
      (E := (cell12574 ⟨13, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (83624651547399 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566819582007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_14 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (20897489499797 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133641157699 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨14, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (20897489499797 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133641157699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_15 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (20888822245327 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (226728633021 / 10000000000000 : ℝ))
      (E := (cell12574 ⟨15, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (20888822245327 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (226728633021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_16 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41760322229773 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566822580011 / 25000000000000 : ℝ))
      (E := (cell12574 ⟨16, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41760322229773 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566822580011 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_17 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41743012199933 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267294290341 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨17, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41743012199933 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267294290341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_18 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (8345142876841 / 10000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133649152257 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨18, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (8345142876841 / 10000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133649152257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_19 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41708428765747 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (453460461869 / 20000000000000 : ℝ))
      (E := (cell12574 ⟨19, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41708428765747 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (453460461869 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

end BstLean.Part268
