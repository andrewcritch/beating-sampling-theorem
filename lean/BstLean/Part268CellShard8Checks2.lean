import BstLean.Part268CellShard8Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12550_40 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (8269650588629 / 10000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270460032149 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨40, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (8269650588629 / 10000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270460032149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_41 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82662455761157 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135232016801 / 50000000000000 : ℝ))
      (E := (cell12550 ⟨41, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82662455761157 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135232016801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_42 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (20657107327999 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (90818722301 / 4000000000000 : ℝ))
      (E := (cell12550 ⟨42, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (20657107327999 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (90818722301 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_43 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41297213254501 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270472044563 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨43, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41297213254501 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270472044563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_44 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82560447322519 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454095210541 / 20000000000000 : ℝ))
      (E := (cell12550 ⟨44, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82560447322519 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454095210541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_45 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82526491723041 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (70952500691 / 3125000000000 : ℝ))
      (E := (cell12550 ⟨45, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82526491723041 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (70952500691 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_46 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82492559681209 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270484069259 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨46, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82492559681209 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270484069259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_47 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82458651167813 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270488075003 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨47, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82458651167813 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270488075003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_48 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82424766153791 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454098407527 / 20000000000000 : ℝ))
      (E := (cell12550 ⟨48, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82424766153791 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (454098407527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_49 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41195452305113 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (3632793717 / 160000000000 : ℝ))
      (E := (cell12550 ⟨49, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41195452305113 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (3632793717 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_50 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82357066508347 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270500061541 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨50, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82357066508347 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270500061541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_51 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (20580812954881 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (227050405953 / 10000000000000 : ℝ))
      (E := (cell12550 ⟨51, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (20580812954881 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (227050405953 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_52 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (20572365128819 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270508064601 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨52, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (20572365128819 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270508064601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_53 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82255692567261 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270512074051 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨53, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82255692567261 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270512074051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_54 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82221947947279 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270516084971 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨54, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82221947947279 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270516084971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_55 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (10273528328409 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270520094239 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨55, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (10273528328409 / 12500000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270520094239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_56 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (20538632144831 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (56763102463 / 2500000000000 : ℝ))
      (E := (cell12550 ⟨56, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (20538632144831 / 25000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (56763102463 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_57 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (41060426887827 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270528094279 / 100000000000000 : ℝ))
      (E := (cell12550 ⟨57, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (41060426887827 / 50000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (2270528094279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_58 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (5130450136789 / 6250000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135266038883 / 50000000000000 : ℝ))
      (E := (cell12550 ⟨58, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (5130450136789 / 6250000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (1135266038883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12550_59 : CellCertificate 12550 (890929151996801 / 10000000000000000 : ℝ) (1673666234746331 / 1000000000000000000 : ℝ) (67634146661539 / 2000000000000000 : ℝ)
    (cell12550 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · norm_num [cell12550]
  · have h := gap_lower (n := 12550) (a := (82053573790731 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (141908506513 / 6250000000000 : ℝ))
      (E := (cell12550 ⟨59, by decide⟩).energy) (xi := (67634146661539 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12550 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12550]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12550])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12550) (a := (82053573790731 / 100000000000000 : ℝ)) (b := (164151987999 / 100000000000000 : ℝ)) (q := (141908506513 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12550])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12550]

theorem cert12551_40 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82696503082517 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (113516573907 / 5000000000000 : ℝ))
      (E := (cell12551 ⟨40, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82696503082517 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (113516573907 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_41 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82662453265627 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567583866509 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨41, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82662453265627 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567583866509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_42 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (16525685424857 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135169738551 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨42, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (16525685424857 / 20000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135169738551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_43 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (20648606157171 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135171725993 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨43, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (20648606157171 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135171725993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_44 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82560445749169 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135173724337 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨44, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82560445749169 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135173724337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_45 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (20631622614059 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270351466177 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨45, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (20631622614059 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270351466177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_46 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41246279360263 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135177722209 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨46, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41246279360263 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135177722209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_47 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82458650512831 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567589860201 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨47, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82458650512831 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567589860201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_48 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (10303095725511 / 12500000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270363453697 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨48, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (10303095725511 / 12500000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270363453697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_49 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41195452282691 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270367481247 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨49, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41195452282691 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270367481247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_50 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (4117853338397 / 5000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270371462421 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨50, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (4117853338397 / 5000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270371462421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_51 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41161626191569 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270375453861 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨51, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41161626191569 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270375453861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_52 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82289461382491 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270379453077 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨52, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82289461382491 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270379453077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_53 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82255693737659 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270383457369 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨53, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82255693737659 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270383457369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_54 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (20555487355111 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135193731911 / 50000000000000 : ℝ))
      (E := (cell12551 ⟨54, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (20555487355111 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (1135193731911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_55 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (20547057100697 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567597867329 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨55, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (20547057100697 / 25000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567597867329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_56 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (41077265328387 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270395470517 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨56, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (41077265328387 / 50000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270395470517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_57 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (656966849237 / 800000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270399523017 / 100000000000000 : ℝ))
      (E := (cell12551 ⟨57, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (656966849237 / 800000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (2270399523017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_58 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82087204868701 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567600876207 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨58, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82087204868701 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567600876207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12551_59 : CellCertificate 12551 (890900572336219 / 10000000000000000 : ℝ) (209191605143503 / 125000000000000000 : ℝ) (338143113796979 / 10000000000000000 : ℝ)
    (cell12551 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · norm_num [cell12551]
  · have h := gap_lower (n := 12551) (a := (82053576771501 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567601882571 / 25000000000000 : ℝ))
      (E := (cell12551 ⟨59, by decide⟩).energy) (xi := (338143113796979 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12551 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12551]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12551])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12551) (a := (82053576771501 / 100000000000000 : ℝ)) (b := (32827749037 / 20000000000000 : ℝ)) (q := (567601882571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12551])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12551]

theorem cert12552_40 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (16539300055931 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270202920817 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨40, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (16539300055931 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270202920817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_41 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (20665612692743 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (45404139079 / 2000000000000 : ℝ))
      (E := (cell12552 ⟨41, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (20665612692743 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (45404139079 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_42 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (8262842493741 / 10000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (70944092257 / 3125000000000 : ℝ))
      (E := (cell12552 ⟨42, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (8262842493741 / 10000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (70944092257 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_43 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (20648605687291 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454042983003 / 20000000000000 : ℝ))
      (E := (cell12552 ⟨43, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (20648605687291 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (454042983003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_44 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82560444176581 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270218959137 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨44, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82560444176581 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270218959137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_45 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (16505297838031 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270222907121 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨45, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (16505297838031 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270222907121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_46 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (8249255776053 / 10000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270226934243 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨46, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (8249255776053 / 10000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270226934243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_47 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82458649858497 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270230921357 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨47, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82458649858497 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270230921357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_48 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (20606191363749 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (90809397027 / 4000000000000 : ℝ))
      (E := (cell12552 ⟨48, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (20606191363749 / 25000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (90809397027 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_49 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82390904521111 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270238945347 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨49, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82390904521111 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270238945347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_50 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82357067028071 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270242919339 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨50, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82357067028071 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270242919339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_51 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82323252947251 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567561740821 / 25000000000000 : ℝ))
      (E := (cell12552 ⟨51, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82323252947251 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567561740821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_52 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (10286182781271 / 12500000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567562739183 / 25000000000000 : ℝ))
      (E := (cell12552 ⟨52, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (10286182781271 / 12500000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567562739183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_53 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41127847454241 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (45405099119 / 2000000000000 : ℝ))
      (E := (cell12552 ⟨53, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41127847454241 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (45405099119 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_54 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82221950893997 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135129479011 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨54, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82221950893997 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135129479011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_55 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (16437646035731 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135131479913 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨55, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (16437646035731 / 20000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135131479913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_56 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82154532734539 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (227026695803 / 10000000000000 : ℝ))
      (E := (cell12552 ⟨56, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82154532734539 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (227026695803 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_57 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (82120858533873 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270270949093 / 100000000000000 : ℝ))
      (E := (cell12552 ⟨57, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (82120858533873 / 100000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (2270270949093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_58 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (41043603774509 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135137494211 / 50000000000000 : ℝ))
      (E := (cell12552 ⟨58, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (41043603774509 / 50000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (1135137494211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12552_59 : CellCertificate 12552 (178174399410629 / 2000000000000000 : ℝ) (836699734405671 / 500000000000000000 : ℝ) (338115498874869 / 10000000000000000 : ℝ)
    (cell12552 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · norm_num [cell12552]
  · have h := gap_lower (n := 12552) (a := (3282143190099 / 4000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567569738443 / 25000000000000 : ℝ))
      (E := (cell12552 ⟨59, by decide⟩).energy) (xi := (338115498874869 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12552 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12552]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12552])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12552) (a := (3282143190099 / 4000000000000 : ℝ)) (b := (164125504527 / 100000000000000 : ℝ)) (q := (567569738443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12552])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12552]

theorem cert12553_40 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41348248738853 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (454014883783 / 20000000000000 : ℝ))
      (E := (cell12553 ⟨40, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41348248738853 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (454014883783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_41 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82662448277191 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270078438593 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨41, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82662448277191 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270078438593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_42 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82628422751371 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270082424111 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨42, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82628422751371 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270082424111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_43 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82594420870443 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567521608413 / 25000000000000 : ℝ))
      (E := (cell12553 ⟨43, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82594420870443 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567521608413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_44 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82560442604753 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (454018093289 / 20000000000000 : ℝ))
      (E := (cell12553 ⟨44, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82560442604753 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (454018093289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_45 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82526487924797 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270094462649 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨45, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82526487924797 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270094462649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_46 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82492556801219 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567524605247 / 25000000000000 : ℝ))
      (E := (cell12553 ⟨46, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82492556801219 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567524605247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_47 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (20614662301203 / 25000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135051228883 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨47, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (20614662301203 / 25000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135051228883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_48 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (16484953021303 / 20000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567526613393 / 25000000000000 : ℝ))
      (E := (cell12553 ⟨48, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (16484953021303 / 20000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (567526613393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_49 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41195452238707 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270110465427 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨49, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41195452238707 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270110465427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_50 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41178533644369 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135057216149 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨50, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41178533644369 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135057216149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_51 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82323253511863 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270118469819 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨51, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82323253511863 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270118469819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_52 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41144731559153 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135061228769 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨52, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41144731559153 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135061228769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_53 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (8225569607973 / 10000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135063225859 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨53, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (8225569607973 / 10000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135063225859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_54 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41110976183969 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135065224723 / 50000000000000 : ℝ))
      (E := (cell12553 ⟨54, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41110976183969 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (1135065224723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_55 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (10273528994359 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (5675336119 / 250000000000 : ℝ))
      (E := (cell12553 ⟨55, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (10273528994359 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (5675336119 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_56 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82154534812617 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (454027700391 / 20000000000000 : ℝ))
      (E := (cell12553 ⟨56, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82154534812617 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (454027700391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_57 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (41060430456699 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270142490773 / 100000000000000 : ℝ))
      (E := (cell12553 ⟨57, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (41060430456699 / 50000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (2270142490773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_58 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (10260901278697 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (141884154337 / 6250000000000 : ℝ))
      (E := (cell12553 ⟨58, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (10260901278697 / 12500000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (141884154337 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12553_59 : CellCertificate 12553 (890843426146527 / 10000000000000000 : ℝ) (1673266117731203 / 1000000000000000000 : ℝ) (338087888540107 / 10000000000000000 : ℝ)
    (cell12553 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · norm_num [cell12553]
  · have h := gap_lower (n := 12553) (a := (82053582733651 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (454030098607 / 20000000000000 : ℝ))
      (E := (cell12553 ⟨59, by decide⟩).energy) (xi := (338087888540107 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12553 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12553]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12553])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12553) (a := (82053582733651 / 100000000000000 : ℝ)) (b := (164112266023 / 100000000000000 : ℝ)) (q := (454030098607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12553])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12553]

theorem cert12554_40 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (20674123669167 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567486493109 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨40, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (20674123669167 / 25000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567486493109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_41 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82662445784283 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269949978719 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨41, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82662445784283 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269949978719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_42 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82628420566169 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567488502581 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨42, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82628420566169 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567488502581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_43 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82594418992521 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269958007897 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨43, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82594418992521 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269958007897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_44 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82560441033687 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269962029421 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨44, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82560441033687 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269962029421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_45 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82526486660163 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269966015057 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨45, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82526486660163 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269966015057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_46 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (16498511168519 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269970022401 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨46, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (16498511168519 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269970022401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_47 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (2576832767243 / 3125000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567493497783 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨47, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (2576832767243 / 3125000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567493497783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_48 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (16484952951729 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (453995607477 / 20000000000000 : ℝ))
      (E := (cell12554 ⟨48, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (16484952951729 / 20000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (453995607477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_49 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (8239090443429 / 10000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269982041487 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨49, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (8239090443429 / 10000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269982041487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_50 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82357067549941 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269986001299 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨50, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82357067549941 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269986001299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_51 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (41161627038487 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269990032457 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨51, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (41161627038487 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2269990032457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_52 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82289463986907 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134997007253 / 50000000000000 : ℝ))
      (E := (cell12554 ⟨52, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82289463986907 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (1134997007253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_53 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82255697251403 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (4433589851 / 195312500000 : ℝ))
      (E := (cell12554 ⟨53, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82255697251403 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (4433589851 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_54 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (41110976921133 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2270001997159 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨54, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (41110976921133 / 50000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2270001997159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_55 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (1027352921643 / 1250000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2270006050809 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨55, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (1027352921643 / 1250000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2270006050809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_56 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82154536891009 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2270010043181 / 100000000000000 : ℝ))
      (E := (cell12554 ⟨56, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82154536891009 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (2270010043181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_57 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (205302158233 / 250000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (70937938431 / 3125000000000 : ℝ))
      (E := (cell12554 ⟨57, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (205302158233 / 250000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (70937938431 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_58 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82087212910373 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567504516513 / 25000000000000 : ℝ))
      (E := (cell12554 ⟨58, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82087212910373 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (567504516513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12554_59 : CellCertificate 12554 (890814859615311 / 10000000000000000 : ℝ) (66925311516101 / 40000000000000000 : ℝ) (84515070697859 / 2500000000000000 : ℝ)
    (cell12554 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · norm_num [cell12554]
  · have h := gap_lower (n := 12554) (a := (82053585715031 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (141876376857 / 6250000000000 : ℝ))
      (E := (cell12554 ⟨59, by decide⟩).energy) (xi := (84515070697859 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12554 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12554]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12554])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12554) (a := (82053585715031 / 100000000000000 : ℝ)) (b := (82049514837 / 50000000000000 : ℝ)) (q := (141876376857 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12554])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12554]

theorem cert12555_40 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41348245938271 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134908790689 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨40, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41348245938271 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134908790689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_41 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (330649773169 / 400000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269821574329 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨41, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (330649773169 / 400000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269821574329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_42 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41314209190901 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453965118661 / 20000000000000 : ℝ))
      (E := (cell12555 ⟨42, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41314209190901 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453965118661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_43 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (82594417115397 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269829578947 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨43, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (82594417115397 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269829578947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_44 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (82560439463381 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134916794621 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨44, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (82560439463381 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134916794621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_45 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (20631621349063 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134918811599 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨45, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (20631621349063 / 25000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134918811599 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_46 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (5155784680291 / 6250000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453968324147 / 20000000000000 : ℝ))
      (E := (cell12555 ⟨46, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (5155784680291 / 6250000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453968324147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_47 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (82458647899387 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567461395089 / 25000000000000 : ℝ))
      (E := (cell12555 ⟨47, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (82458647899387 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (567461395089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_48 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41212382205693 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269849618197 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨48, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41212382205693 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269849618197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_49 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (4119545219587 / 5000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134926807291 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨49, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (4119545219587 / 5000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134926807291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_50 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (514731673823 / 625000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269857626343 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨50, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (514731673823 / 625000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269857626343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_51 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (10290406830323 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134930796103 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨51, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (10290406830323 / 12500000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134930796103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_52 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (8228946485597 / 10000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269865627641 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨52, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (8228946485597 / 10000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269865627641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_53 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (82255698423501 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269869611933 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨53, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (82255698423501 / 100000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269869611933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_54 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41110977658491 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (56746840029 / 2500000000000 : ℝ))
      (E := (cell12555 ⟨54, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41110977658491 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (56746840029 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_55 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41094117754179 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269877651283 / 100000000000000 : ℝ))
      (E := (cell12555 ⟨55, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41094117754179 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (2269877651283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_56 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (16430907793943 / 20000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134940820409 / 50000000000000 : ℝ))
      (E := (cell12555 ⟨56, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (16430907793943 / 20000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (1134940820409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_57 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41060432836639 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453977125057 / 20000000000000 : ℝ))
      (E := (cell12555 ⟨57, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41060432836639 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453977125057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_58 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (8208721559141 / 10000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (226988966009 / 10000000000000 : ℝ))
      (E := (cell12555 ⟨58, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (8208721559141 / 10000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (226988966009 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12555_59 : CellCertificate 12555 (890786297458443 / 10000000000000000 : ℝ) (1672999479320229 / 1000000000000000000 : ℝ) (338032681627597 / 10000000000000000 : ℝ)
    (cell12555 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · norm_num [cell12555]
  · have h := gap_lower (n := 12555) (a := (41026794348307 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453978724597 / 20000000000000 : ℝ))
      (E := (cell12555 ⟨59, by decide⟩).energy) (xi := (338032681627597 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12555 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12555]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12555])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12555) (a := (41026794348307 / 50000000000000 : ℝ)) (b := (164085795479 / 100000000000000 : ℝ)) (q := (453978724597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12555])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12555]

theorem cert12556_40 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82696489077327 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453937849149 / 20000000000000 : ℝ))
      (E := (cell12556 ⟨40, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82696489077327 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453937849149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_41 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (8266244080109 / 10000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134846612713 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨41, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (8266244080109 / 10000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134846612713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_42 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (645534501549 / 781250000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269697231833 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨42, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (645534501549 / 781250000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269697231833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_43 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (8259441523907 / 10000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269701264413 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨43, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (8259441523907 / 10000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269701264413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_44 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (16512087578767 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269705263563 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨44, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (16512087578767 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269705263563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_45 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82526484133063 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (90788369129 / 4000000000000 : ℝ))
      (E := (cell12556 ⟨45, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82526484133063 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (90788369129 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_46 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41246276963701 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134856637433 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨46, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41246276963701 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134856637433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_47 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82458647247647 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134858612719 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨47, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82458647247647 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134858612719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_48 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41212382032369 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (141857578433 / 6250000000000 : ℝ))
      (E := (cell12556 ⟨48, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41212382032369 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (141857578433 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_49 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82390904349763 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269725243659 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨49, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82390904349763 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269725243659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_50 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (20589267018489 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134864624231 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨50, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (20589267018489 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134864624231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_51 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (20580813802173 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453946653411 / 20000000000000 : ℝ))
      (E := (cell12556 ⟨51, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (20580813802173 / 25000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (453946653411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_52 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41144732862747 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269737237927 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨52, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41144732862747 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269737237927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_53 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82255699596023 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269741276383 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨53, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82255699596023 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269741276383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_54 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (16444391358417 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567436315363 / 25000000000000 : ℝ))
      (E := (cell12556 ⟨54, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (16444391358417 / 20000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567436315363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_55 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82188237285627 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134874624511 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨55, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82188237285627 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134874624511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_56 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (41077270524367 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567438323717 / 25000000000000 : ℝ))
      (E := (cell12556 ⟨56, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (41077270524367 / 50000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (567438323717 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_57 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82120868053633 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269757277251 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨57, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82120868053633 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269757277251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_58 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (82087218272687 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269761310663 / 100000000000000 : ℝ))
      (E := (cell12556 ⟨58, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (82087218272687 / 100000000000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (2269761310663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12556_59 : CellCertificate 12556 (111344717459359 / 1250000000000000 : ℝ) (334573238395847 / 200000000000000000 : ℝ) (169002542523667 / 5000000000000000 : ℝ)
    (cell12556 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · norm_num [cell12556]
  · have h := gap_lower (n := 12556) (a := (51283494799 / 62500000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134882636427 / 50000000000000 : ℝ))
      (E := (cell12556 ⟨59, by decide⟩).energy) (xi := (169002542523667 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12556 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12556]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12556])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12556) (a := (51283494799 / 62500000000 : ℝ)) (b := (164072563437 / 100000000000000 : ℝ)) (q := (1134882636427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12556])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12556]

theorem cert12557_40 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82696486279023 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269560906803 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨40, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82696486279023 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269560906803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_41 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82662438310803 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (226956493201 / 10000000000000 : ℝ))
      (E := (cell12557 ⟨41, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82662438310803 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (226956493201 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_42 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (10328551751947 / 12500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269568925911 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨42, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (10328551751947 / 12500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269568925911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_43 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41297206681771 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453914589337 / 20000000000000 : ℝ))
      (E := (cell12557 ⟨43, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41297206681771 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (453914589337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_44 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82560436325049 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269576934731 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨44, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82560436325049 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269576934731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_45 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82526482870597 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269580947837 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨45, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82526482870597 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269580947837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_46 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41246276485417 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269584925919 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨46, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41246276485417 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269584925919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_47 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41229323298277 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (113479446319 / 5000000000000 : ℝ))
      (E := (cell12557 ⟨47, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41229323298277 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (113479446319 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_48 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82424763718699 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269592947581 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨48, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82424763718699 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269592947581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_49 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82390904308359 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (28369961609 / 1250000000000 : ℝ))
      (E := (cell12557 ⟨49, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82390904308359 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (28369961609 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_50 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82357068336767 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (18156807413 / 800000000000 : ℝ))
      (E := (cell12557 ⟨50, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82357068336767 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (18156807413 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_51 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82323255775299 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (283700617377 / 12500000000000 : ℝ))
      (E := (cell12557 ⟨51, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82323255775299 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (283700617377 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_52 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82289466595479 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269608963397 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨52, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82289466595479 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269608963397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_53 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82255700768969 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (283701617253 / 12500000000000 : ℝ))
      (E := (cell12557 ⟨53, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82255700768969 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (283701617253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_54 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (10277744783447 / 12500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134808489017 / 50000000000000 : ℝ))
      (E := (cell12557 ⟨54, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (10277744783447 / 12500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134808489017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_55 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41094119531623 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269620962199 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨55, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41094119531623 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269620962199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_56 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (41077271564033 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269624946223 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨56, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (41077271564033 / 50000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269624946223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_57 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (10265108804283 / 12500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269628985693 / 100000000000000 : ℝ))
      (E := (cell12557 ⟨57, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (10265108804283 / 12500000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (2269628985693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_58 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (82087220954203 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (283704119827 / 12500000000000 : ℝ))
      (E := (cell12557 ⟨58, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (82087220954203 / 100000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (283704119827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12557_59 : CellCertificate 12557 (890729186263543 / 10000000000000000 : ℝ) (1672732925874469 / 1000000000000000000 : ℝ) (337977493049391 / 10000000000000000 : ℝ)
    (cell12557 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · norm_num [cell12557]
  · have h := gap_lower (n := 12557) (a := (20513398665097 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134818489661 / 50000000000000 : ℝ))
      (E := (cell12557 ⟨59, by decide⟩).energy) (xi := (337977493049391 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12557 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12557]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12557])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12557) (a := (20513398665097 / 25000000000000 : ℝ)) (b := (41014833387 / 25000000000000 : ℝ)) (q := (1134818489661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12557])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12557]

theorem cert12558_40 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82696483481629 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134716341011 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨40, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82696483481629 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134716341011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_41 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82662435821389 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134718317663 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨41, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82662435821389 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134718317663 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_42 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (20657102958429 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269440675541 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨42, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (20657102958429 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269440675541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_43 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82594411488811 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567361171143 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨43, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82594411488811 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567361171143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_44 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (2580013586157 / 3125000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269448661573 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨44, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (2580013586157 / 3125000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269448661573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_45 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (41263240804427 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453890532867 / 20000000000000 : ℝ))
      (E := (cell12558 ⟨45, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (41263240804427 / 50000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453890532867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_46 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (1649851040299 / 2000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269456691647 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨46, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (1649851040299 / 2000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269456691647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_47 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (20614661486527 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (141841292699 / 6250000000000 : ℝ))
      (E := (cell12558 ⟨47, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (20614661486527 / 25000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (141841292699 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_48 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82424763373271 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269464696157 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨48, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82424763373271 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269464696157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_49 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (10298863033441 / 12500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453893733953 / 20000000000000 : ℝ))
      (E := (cell12558 ⟨49, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (10298863033441 / 12500000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453893733953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_50 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82357068600113 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567368165209 / 25000000000000 : ℝ))
      (E := (cell12558 ⟨50, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82357068600113 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (567368165209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_51 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (16464651268481 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134738333543 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨51, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (16464651268481 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134738333543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_52 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (3291578698637 / 4000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134740343011 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨52, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (3291578698637 / 4000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134740343011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_53 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82255701942339 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (283685589367 / 12500000000000 : ℝ))
      (E := (cell12558 ⟨53, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82255701942339 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (283685589367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_54 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82221959743453 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269488691847 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨54, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82221959743453 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269488691847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_55 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (16437648168243 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453898534529 / 20000000000000 : ℝ))
      (E := (cell12558 ⟨55, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (16437648168243 / 20000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (453898534529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_56 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (2567329537741 / 3125000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134748356551 / 50000000000000 : ℝ))
      (E := (cell12558 ⟨56, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (2567329537741 / 3125000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (1134748356551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_57 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82120872815171 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269500691479 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨57, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82120872815171 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269500691479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_58 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82087223635959 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (283688090283 / 12500000000000 : ℝ))
      (E := (cell12558 ⟨58, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82087223635959 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (283688090283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12558_59 : CellCertificate 12558 (445350318611703 / 5000000000000000 : ℝ) (334519936200171 / 200000000000000000 : ℝ) (1320116818877 / 39062500000000 : ℝ)
    (cell12558 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · norm_num [cell12558]
  · have h := gap_lower (n := 12558) (a := (82053597642579 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269508742389 / 100000000000000 : ℝ))
      (E := (cell12558 ⟨59, by decide⟩).energy) (xi := (1320116818877 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12558 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12558]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12558])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12558) (a := (82053597642579 / 100000000000000 : ℝ)) (b := (16404610581 / 10000000000000 : ℝ)) (q := (2269508742389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12558])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12558]

theorem cert12559_40 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41348240342573 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134652226967 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨40, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41348240342573 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134652226967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_41 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82662433332847 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (283663556611 / 12500000000000 : ℝ))
      (E := (cell12559 ⟨41, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82662433332847 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (283663556611 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_42 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82628409652691 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (113465621097 / 5000000000000 : ℝ))
      (E := (cell12559 ⟨42, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82628409652691 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (113465621097 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_43 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82594409614877 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134658209633 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨43, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82594409614877 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134658209633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_44 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41280216594879 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269320444091 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨44, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41280216594879 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269320444091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_45 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82526480347833 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (226932443657 / 10000000000000 : ℝ))
      (E := (cell12559 ⟨45, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82526480347833 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (226932443657 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_46 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82492551059751 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134664227149 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨46, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82492551059751 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134664227149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_47 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (8245864529631 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269332436949 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨47, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (8245864529631 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269332436949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_48 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82424763028453 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269336441733 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨48, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82424763028453 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269336441733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_49 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82390904227269 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134670233397 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨49, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82390904227269 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134670233397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_50 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (16471413772799 / 20000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269344451091 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨50, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (16471413772799 / 20000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269344451091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_51 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (10290407113751 / 12500000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (35458569551 / 1562500000000 : ℝ))
      (E := (cell12559 ⟨51, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (10290407113751 / 12500000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (35458569551 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_52 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82289468336833 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134676232407 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨52, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82289468336833 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134676232407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_53 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (82255703116133 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134678244519 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨53, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (82255703116133 / 100000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134678244519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_54 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41110980609859 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269360461951 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨54, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41110980609859 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269360461951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_55 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41094121309767 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269364498529 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨55, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41094121309767 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269364498529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_56 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (8215454728767 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269368477287 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨56, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (8215454728767 / 10000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269368477287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_57 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (16424175039271 / 20000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269372512873 / 100000000000000 : ℝ))
      (E := (cell12559 ⟨57, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (16424175039271 / 20000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (2269372512873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_58 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (41043613158977 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567344120823 / 25000000000000 : ℝ))
      (E := (cell12559 ⟨58, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (41043613158977 / 50000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (567344120823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12559_59 : CellCertificate 12559 (890672092553409 / 10000000000000000 : ℝ) (41811661433833 / 25000000000000000 : ℝ) (337922322795441 / 10000000000000000 : ℝ)
    (cell12559 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · norm_num [cell12559]
  · have h := gap_lower (n := 12559) (a := (20513400156243 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134690251437 / 50000000000000 : ℝ))
      (E := (cell12559 ⟨59, by decide⟩).energy) (xi := (337922322795441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12559 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12559]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12559])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12559) (a := (20513400156243 / 25000000000000 : ℝ)) (b := (6561315209 / 4000000000000 : ℝ)) (q := (1134690251437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12559])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12559]

theorem cert12560_40 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82696477889573 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134588140637 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨40, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82696477889573 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134588140637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_41 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41331215422589 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (141823766699 / 6250000000000 : ℝ))
      (E := (cell12560 ⟨41, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41331215422589 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (141823766699 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_42 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (33051362989 / 40000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134592141337 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨42, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (33051362989 / 40000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134592141337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_43 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82594407741741 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (113459413419 / 5000000000000 : ℝ))
      (E := (cell12560 ⟨43, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82594407741741 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (113459413419 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_44 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82560431623251 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134596141143 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨44, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82560431623251 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134596141143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_45 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82526479087533 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453839252909 / 20000000000000 : ℝ))
      (E := (cell12560 ⟨45, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82526479087533 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453839252909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_46 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82492550105237 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269200272751 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨46, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82492550105237 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269200272751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_47 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82458644647159 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134602123289 / 50000000000000 : ℝ))
      (E := (cell12560 ⟨47, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82458644647159 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (1134602123289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_48 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (20606190671061 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269208302157 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨48, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (20606190671061 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269208302157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_49 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82390904187583 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453842452173 / 20000000000000 : ℝ))
      (E := (cell12560 ⟨49, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82390904187583 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453842452173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_50 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (20589267282103 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453843259479 / 20000000000000 : ℝ))
      (E := (cell12560 ⟨50, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (20589267282103 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453843259479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_51 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (8232325747811 / 10000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269220291551 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨51, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (8232325747811 / 10000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269220291551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_52 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82289469208201 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269224299779 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨52, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82289469208201 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269224299779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_53 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82255704290351 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269228319373 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨53, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82255704290351 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269228319373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_54 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82221962696369 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (45384645767 / 2000000000000 : ℝ))
      (E := (cell12560 ⟨54, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82221962696369 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (45384645767 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_55 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41094122199101 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453847264337 / 20000000000000 : ℝ))
      (E := (cell12560 ⟨55, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41094122199101 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (453847264337 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_56 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (82154549367941 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269240297889 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨56, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (82154549367941 / 100000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269240297889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_57 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (41060438788907 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269244331613 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨57, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (41060438788907 / 50000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269244331613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_58 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (20521807250047 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (113462415043 / 5000000000000 : ℝ))
      (E := (cell12560 ⟨58, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (20521807250047 / 25000000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (113462415043 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12560_59 : CellCertificate 12560 (356257420901 / 4000000000000 : ℝ) (1672333254926793 / 1000000000000000000 : ℝ) (13515789781477 / 400000000000000 : ℝ)
    (cell12560 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · norm_num [cell12560]
  · have h := gap_lower (n := 12560) (a := (5128350225473 / 6250000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269252319959 / 100000000000000 : ℝ))
      (E := (cell12560 ⟨59, by decide⟩).energy) (xi := (13515789781477 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12560 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12560]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12560])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12560) (a := (5128350225473 / 6250000000000 : ℝ)) (b := (16401965679 / 10000000000000 : ℝ)) (q := (2269252319959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12560])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12560]

theorem cert12561_40 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82696475094909 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269048105311 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨40, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82696475094909 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269048105311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_41 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82662428358381 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567263034243 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨41, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82662428358381 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567263034243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_42 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (10328550661643 / 12500000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (113452807009 / 5000000000000 : ℝ))
      (E := (cell12561 ⟨42, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (10328550661643 / 12500000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (113452807009 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_43 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82594405869401 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (453812022861 / 20000000000000 : ℝ))
      (E := (cell12561 ⟨43, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82594405869401 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (453812022861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_44 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (2580013439297 / 3125000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226906411733 / 10000000000000 : ℝ))
      (E := (cell12561 ⟨44, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (2580013439297 / 3125000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226906411733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_45 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (20631619456989 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269068148259 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨45, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (20631619456989 / 25000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269068148259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_46 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41246274575703 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (453814429401 / 20000000000000 : ℝ))
      (E := (cell12561 ⟨46, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41246274575703 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (453814429401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_47 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41229321999327 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226907611207 / 10000000000000 : ℝ))
      (E := (cell12561 ⟨47, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41229321999327 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (226907611207 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_48 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (16484952468129 / 20000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269080159583 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨48, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (16484952468129 / 20000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269080159583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_49 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82390904148469 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567271042467 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨49, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82390904148469 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567271042467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_50 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82357069393363 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (113454407039 / 5000000000000 : ℝ))
      (E := (cell12561 ⟨50, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82357069393363 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (113454407039 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_51 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82323258046709 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567273032239 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨51, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82323258046709 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567273032239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_52 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (8228947008003 / 10000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269096131899 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨52, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (8228947008003 / 10000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269096131899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_53 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (2570490795781 / 3125000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134550073451 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨53, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (2570490795781 / 3125000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134550073451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_54 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41110982086703 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567276042761 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨54, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41110982086703 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567276042761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_55 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (4109412308861 / 5000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269108142109 / 100000000000000 : ℝ))
      (E := (cell12561 ⟨55, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (4109412308861 / 5000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (2269108142109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_56 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (3286182057941 / 4000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567278043727 / 25000000000000 : ℝ))
      (E := (cell12561 ⟨56, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (3286182057941 / 4000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (567278043727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_57 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82120879959549 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134558073849 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨57, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82120879959549 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134558073849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_58 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (82087231682661 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (283640021871 / 12500000000000 : ℝ))
      (E := (cell12561 ⟨58, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (82087231682661 / 100000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (283640021871 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12561_59 : CellCertificate 12561 (222653754079907 / 2500000000000000 : ℝ) (836100036858101 / 500000000000000000 : ℝ) (337867170855709 / 10000000000000000 : ℝ)
    (cell12561 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · norm_num [cell12561]
  · have h := gap_lower (n := 12561) (a := (41026803295183 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134562096823 / 50000000000000 : ℝ))
      (E := (cell12561 ⟨59, by decide⟩).energy) (xi := (337867170855709 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12561 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12561]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12561])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12561) (a := (41026803295183 / 50000000000000 : ℝ)) (b := (82003217753 / 50000000000000 : ℝ)) (q := (1134562096823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12561])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12561]

theorem cert12562_40 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (16539294460231 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268920043511 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨40, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (16539294460231 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268920043511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_41 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (16532485174491 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567231015563 / 25000000000000 : ℝ))
      (E := (cell12562 ⟨41, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (16532485174491 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567231015563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_42 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41314201557311 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (56723201331 / 2500000000000 : ℝ))
      (E := (cell12562 ⟨42, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41314201557311 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (56723201331 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_43 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82594403997857 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283616501981 / 12500000000000 : ℝ))
      (E := (cell12562 ⟨43, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82594403997857 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283616501981 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_44 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (20640107123129 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268936066881 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨44, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (20640107123129 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268936066881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_45 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82526476569099 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268940028863 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨45, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82526476569099 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268940028863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_46 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (4124627409913 / 5000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268944018187 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨46, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (4124627409913 / 5000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268944018187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_47 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (20614660837699 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268948033427 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨47, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (20614660837699 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268948033427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_48 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (16484952399531 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283619009117 / 12500000000000 : ℝ))
      (E := (cell12562 ⟨48, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (16484952399531 / 20000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283619009117 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_49 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82390904109927 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268956075913 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨49, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82390904109927 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268956075913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_50 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (1647141393177 / 2000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268960040213 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨50, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (1647141393177 / 2000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268960040213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_51 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41161629307903 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283620510183 / 12500000000000 : ℝ))
      (E := (cell12562 ⟨51, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41161629307903 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283620510183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_52 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82289470952319 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283621009901 / 12500000000000 : ℝ))
      (E := (cell12562 ⟨52, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82289470952319 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (283621009901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_53 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82255706640057 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (453794417941 / 20000000000000 : ℝ))
      (E := (cell12562 ⟨53, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82255706640057 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (453794417941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_54 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (8222196565083 / 10000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (226897605097 / 10000000000000 : ℝ))
      (E := (cell12562 ⟨54, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (8222196565083 / 10000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (226897605097 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_55 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82188247956587 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268980077977 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨55, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82188247956587 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268980077977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_56 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82154553529421 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567246012309 / 25000000000000 : ℝ))
      (E := (cell12562 ⟨56, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82154553529421 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (567246012309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_57 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (82120882341559 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268988079397 / 100000000000000 : ℝ))
      (E := (cell12562 ⟨57, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (82120882341559 / 100000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (2268988079397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_58 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (20521808591343 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134496052809 / 50000000000000 : ℝ))
      (E := (cell12562 ⟨58, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (20521808591343 / 25000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134496052809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12562_59 : CellCertificate 12562 (890586484753743 / 10000000000000000 : ℝ) (1306302276341 / 781250000000000 : ℝ) (337839601750541 / 10000000000000000 : ℝ)
    (cell12562 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · norm_num [cell12562]
  · have h := gap_lower (n := 12562) (a := (41026804786683 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134498032377 / 50000000000000 : ℝ))
      (E := (cell12562 ⟨59, by decide⟩).energy) (xi := (337839601750541 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12562 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12562]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12562])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12562) (a := (41026804786683 / 50000000000000 : ℝ)) (b := (40998304093 / 25000000000000 : ℝ)) (q := (1134498032377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12562])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12562]

theorem cert12563_40 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (82696469508311 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (283598997301 / 12500000000000 : ℝ))
      (E := (cell12563 ⟨40, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (82696469508311 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (283598997301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_41 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41331211693701 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268795984267 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨41, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41331211693701 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268795984267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_42 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (82628400936933 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567199990769 / 25000000000000 : ℝ))
      (E := (cell12563 ⟨42, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (82628400936933 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567199990769 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_43 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (8259440212711 / 10000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268803973007 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨43, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (8259440212711 / 10000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268803973007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_44 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41280213464143 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567202003321 / 25000000000000 : ℝ))
      (E := (cell12563 ⟨44, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41280213464143 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567202003321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_45 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (20631618827741 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268812024059 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨45, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (20631618827741 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268812024059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_46 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (82492547245797 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268816004047 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨46, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (82492547245797 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268816004047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_47 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (16491728540717 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (283602501331 / 12500000000000 : ℝ))
      (E := (cell12563 ⟨47, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (16491728540717 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (283602501331 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_48 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41212380827637 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268823983293 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨48, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41212380827637 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268823983293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_49 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (20597726017989 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268827979001 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨49, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (20597726017989 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268827979001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_50 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (82357069924871 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (141801999731 / 6250000000000 : ℝ))
      (E := (cell12563 ⟨50, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (82357069924871 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (141801999731 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_51 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (411616295927 / 500000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567209007773 / 25000000000000 : ℝ))
      (E := (cell12563 ⟨51, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (411616295927 / 500000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567209007773 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_52 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (20572367956267 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (90753600947 / 4000000000000 : ℝ))
      (E := (cell12563 ⟨52, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (20572367956267 / 25000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (90753600947 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_53 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (16451141563109 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268844029703 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨53, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (16451141563109 / 20000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268844029703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_54 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (256943647277 / 312500000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (141803002891 / 6250000000000 : ℝ))
      (E := (cell12563 ⟨54, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (256943647277 / 312500000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (141803002891 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_55 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (5136765608519 / 6250000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567213002779 / 25000000000000 : ℝ))
      (E := (cell12563 ⟨55, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (5136765608519 / 6250000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (567213002779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_56 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (82154555610629 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268856039093 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨56, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (82154555610629 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268856039093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_57 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (41060442361923 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268860008441 / 100000000000000 : ℝ))
      (E := (cell12563 ⟨57, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (41060442361923 / 50000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (2268860008441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_58 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (82087237048323 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (45377280673 / 2000000000000 : ℝ))
      (E := (cell12563 ⟨58, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (82087237048323 / 100000000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (45377280673 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12563_59 : CellCertificate 12563 (890557957553793 / 10000000000000000 : ℝ) (1671933774922561 / 1000000000000000000 : ℝ) (168906018610083 / 5000000000000000 : ℝ)
    (cell12563 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · norm_num [cell12563]
  · have h := gap_lower (n := 12563) (a := (10256701569571 / 12500000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134434025823 / 50000000000000 : ℝ))
      (E := (cell12563 ⟨59, by decide⟩).energy) (xi := (168906018610083 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12563 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12563]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12563])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12563) (a := (10256701569571 / 12500000000000 : ℝ)) (b := (40994999847 / 25000000000000 : ℝ)) (q := (1134434025823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12563])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12563]

theorem cert12564_40 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (661571733731 / 800000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268663968739 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨40, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (661571733731 / 800000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268663968739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_41 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82662420903219 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134333980889 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨41, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82662420903219 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134333980889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_42 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82628398760079 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268671987249 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨42, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82628398760079 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268671987249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_43 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82594400257159 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268675985787 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨43, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82594400257159 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268675985787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_44 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (16512085072963 / 20000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (283585001921 / 12500000000000 : ℝ))
      (E := (cell12564 ⟨44, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (16512085072963 / 20000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (283585001921 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_45 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (1650529481071 / 2000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268684016147 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨45, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (1650529481071 / 2000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268684016147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_46 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41246273147009 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134343993419 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨46, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41246273147009 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134343993419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_47 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82458642057019 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134345992419 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨47, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82458642057019 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134345992419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_48 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82424761313501 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268696008503 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨48, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82424761313501 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268696008503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_49 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82390904034557 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134349998513 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨49, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82390904034557 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134349998513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_50 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41178535095713 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (35448500113 / 1562500000000 : ℝ))
      (E := (cell12564 ⟨50, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41178535095713 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (35448500113 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_51 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82323259755491 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268707977841 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨51, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82323259755491 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268707977841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_52 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (41144736349139 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268712024317 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨52, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (41144736349139 / 50000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268712024317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_53 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (2570490905983 / 3125000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134358012969 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨53, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (2570490905983 / 3125000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134358012969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_54 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (20555492151709 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268720038777 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨54, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (20555492151709 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268720038777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_55 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (8218825151637 / 10000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134362000307 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨55, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (8218825151637 / 10000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134362000307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_56 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (1643091153843 / 2000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (113436401313 / 5000000000000 : ℝ))
      (E := (cell12564 ⟨56, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (1643091153843 / 2000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (113436401313 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_57 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (82120887106407 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268732053103 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨57, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (82120887106407 / 100000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268732053103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_58 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (10260904966439 / 12500000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268736018227 / 100000000000000 : ℝ))
      (E := (cell12564 ⟨58, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (10260904966439 / 12500000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (2268736018227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12564_59 : CellCertificate 12564 (89052943471873 / 1000000000000000 : ℝ) (1671800657329379 / 1000000000000000000 : ℝ) (67556895452667 / 2000000000000000 : ℝ)
    (cell12564 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · norm_num [cell12564]
  · have h := gap_lower (n := 12564) (a := (20513403884993 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134370017981 / 50000000000000 : ℝ))
      (E := (cell12564 ⟨59, by decide⟩).energy) (xi := (67556895452667 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12564 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12564]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12564])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12564) (a := (20513403884993 / 25000000000000 : ℝ)) (b := (20495848069 / 12500000000000 : ℝ)) (q := (1134370017981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12564])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12564]

theorem cert12565_40 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (20674115981337 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (283567001813 / 12500000000000 : ℝ))
      (E := (cell12565 ⟨40, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (20674115981337 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (283567001813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_41 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82662418419907 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134269997393 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨41, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82662418419907 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134269997393 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_42 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82628396584057 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268544008201 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨42, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82628396584057 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268544008201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_43 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (20648599597001 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134274027093 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨43, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (20648599597001 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134274027093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_44 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41280211901051 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268552014307 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨44, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41280211901051 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268552014307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_45 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82526472796857 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (283569500641 / 12500000000000 : ℝ))
      (E := (cell12565 ⟨45, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82526472796857 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (283569500641 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_46 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41246272671461 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134280012717 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨46, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41246272671461 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134280012717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_47 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (824586414111 / 1000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (141785250931 / 6250000000000 : ℝ))
      (E := (cell12565 ⟨47, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (824586414111 / 1000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (141785250931 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_48 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41212380486169 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268568030719 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨48, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41212380486169 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268568030719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_49 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (8239090399773 / 10000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (35446437689 / 1562500000000 : ℝ))
      (E := (cell12565 ⟨49, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (8239090399773 / 10000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (35446437689 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_50 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (20589267614629 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567144003963 / 25000000000000 : ℝ))
      (E := (cell12565 ⟨50, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (20589267614629 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567144003963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_51 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82323260326079 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134290019849 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨51, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82323260326079 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134290019849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_52 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82289473571947 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268584022119 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨52, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82289473571947 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268584022119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_53 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82255710167789 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567147019603 / 25000000000000 : ℝ))
      (E := (cell12565 ⟨53, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82255710167789 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (567147019603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_54 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41110985042709 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268592028533 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨54, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41110985042709 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268592028533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_55 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (5136765831049 / 6250000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134298023237 / 50000000000000 : ℝ))
      (E := (cell12565 ⟨55, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (5136765831049 / 6250000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (1134298023237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_56 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (41077279886991 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268600069851 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨56, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (41077279886991 / 50000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268600069851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_57 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (20530222372311 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268604095113 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨57, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (20530222372311 / 25000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268604095113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_58 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82087242414939 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268608059349 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨58, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82087242414939 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268608059349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12565_59 : CellCertificate 12565 (445250458123751 / 5000000000000000 : ℝ) (167166756093187 / 100000000000000000 : ℝ) (168878460939397 / 5000000000000000 : ℝ)
    (cell12565 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · norm_num [cell12565]
  · have h := gap_lower (n := 12565) (a := (82053618523577 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268612076883 / 100000000000000 : ℝ))
      (E := (cell12565 ⟨59, by decide⟩).energy) (xi := (168878460939397 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12565 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12565]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12565])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12565) (a := (82053618523577 / 100000000000000 : ℝ)) (b := (20494196483 / 12500000000000 : ℝ)) (q := (2268612076883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12565])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12565]

theorem cert12566_40 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (8269646113523 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134204057851 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨40, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (8269646113523 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134204057851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_41 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (82662415937467 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (283551510411 / 12500000000000 : ℝ))
      (E := (cell12566 ⟨41, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (82662415937467 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (283551510411 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_42 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (82628394408869 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268416084709 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨42, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (82628394408869 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268416084709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_43 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20648599129911 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268420119401 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨43, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20648599129911 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268420119401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_44 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (82560422240147 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (453684825551 / 20000000000000 : ℝ))
      (E := (cell12566 ⟨44, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (82560422240147 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (453684825551 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_45 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20631617885221 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (70888378397 / 3125000000000 : ℝ))
      (E := (cell12566 ⟨45, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20631617885221 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (70888378397 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_46 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (8249254439251 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567108029959 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨46, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (8249254439251 / 10000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567108029959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_47 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (41229320382913 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268436100821 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨47, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (41229320382913 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268436100821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_48 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (41212380315891 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (453688021773 / 20000000000000 : ℝ))
      (E := (cell12566 ⟨48, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (41212380315891 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (453688021773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_49 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (82390903961473 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (283555517763 / 12500000000000 : ℝ))
      (E := (cell12566 ⟨49, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (82390903961473 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (283555517763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_50 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (82357070726139 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134224069747 / 50000000000000 : ℝ))
      (E := (cell12566 ⟨50, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (82357070726139 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (1134224069747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_51 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20580815224291 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567113024669 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨51, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20580815224291 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567113024669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_52 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20572368611519 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268456135113 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨52, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20572368611519 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268456135113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_53 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (41127855672273 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268460128081 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨53, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (41127855672273 / 50000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268460128081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_54 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (16444394312877 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567116033413 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨54, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (16444394312877 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567116033413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_55 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (20547063769387 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567117037173 / 25000000000000 : ℝ))
      (E := (cell12566 ⟨55, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (20547063769387 / 25000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (567117037173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_56 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (82154561856127 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268472169861 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨56, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (82154561856127 / 100000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268472169861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_57 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (16424178374471 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268476134473 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨57, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (16424178374471 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268476134473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_58 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (16417449019721 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268480157013 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨58, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (16417449019721 / 20000000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268480157013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12566_59 : CellCertificate 12566 (445236201069531 / 5000000000000000 : ℝ) (417883621431243 / 250000000000000000 : ℝ) (84432342766323 / 2500000000000000 : ℝ)
    (cell12566 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · norm_num [cell12566]
  · have h := gap_lower (n := 12566) (a := (10256702688423 / 12500000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268484174409 / 100000000000000 : ℝ))
      (E := (cell12566 ⟨59, by decide⟩).energy) (xi := (84432342766323 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12566 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12566]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12566])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12566) (a := (10256702688423 / 12500000000000 : ℝ)) (b := (6557614453 / 4000000000000 : ℝ)) (q := (2268484174409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12566])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12566]

theorem cert12567_40 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (4134822917301 / 5000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268280213603 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨40, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (4134822917301 / 5000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268280213603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_41 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (10332801681987 / 12500000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268284227291 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨41, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (10332801681987 / 12500000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268284227291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_42 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41314196117257 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268288216779 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨42, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41314196117257 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268288216779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_43 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82594394652079 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268292240239 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨43, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82594394652079 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268292240239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_44 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (1651208413579 / 2000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (113414811903 / 5000000000000 : ℝ))
      (E := (cell12567 ⟨44, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (1651208413579 / 2000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (113414811903 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_45 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82526470285631 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (283537526147 / 12500000000000 : ℝ))
      (E := (cell12567 ⟨45, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82526470285631 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (283537526147 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_46 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (4124627172139 / 5000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567076052793 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨46, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (4124627172139 / 5000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567076052793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_47 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41229320060599 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268308242617 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨47, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41229320060599 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268308242617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_48 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (16484952058367 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134156121471 / 50000000000000 : ℝ))
      (E := (cell12567 ⟨48, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (16484952058367 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134156121471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_49 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (20597725981447 / 25000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268316269159 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨49, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (20597725981447 / 25000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268316269159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_50 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (10294633874287 / 12500000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134160130111 / 50000000000000 : ℝ))
      (E := (cell12567 ⟨50, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (10294633874287 / 12500000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134160130111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_51 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41161630734373 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567081068191 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨51, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41161630734373 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567081068191 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_52 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (16457895064133 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567082061317 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨52, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (16457895064133 / 20000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567082061317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_53 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (20563928130431 / 25000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (283541529249 / 12500000000000 : ℝ))
      (E := (cell12567 ⟨53, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (20563928130431 / 25000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (283541529249 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_54 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41110986521869 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268336236009 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨54, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41110986521869 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268336236009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_55 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82188256858659 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567085062047 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨55, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82188256858659 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567085062047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_56 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82154563938583 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134172133593 / 50000000000000 : ℝ))
      (E := (cell12567 ⟨56, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82154563938583 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134172133593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_57 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (41060447127871 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268348289451 / 100000000000000 : ℝ))
      (E := (cell12567 ⟨57, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (41060447127871 / 50000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (2268348289451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_58 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (20521811945627 / 25000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567088063017 / 25000000000000 : ℝ))
      (E := (cell12567 ⟨58, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (20521811945627 / 25000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (567088063017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12567_59 : CellCertificate 12567 (22261097309809 / 250000000000000 : ℝ) (835700715851813 / 500000000000000000 : ℝ) (337701824821581 / 10000000000000000 : ℝ)
    (cell12567 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · norm_num [cell12567]
  · have h := gap_lower (n := 12567) (a := (82053624491393 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134178134681 / 50000000000000 : ℝ))
      (E := (cell12567 ⟨59, by decide⟩).energy) (xi := (337701824821581 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12567 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12567]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12567])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12567) (a := (82053624491393 / 100000000000000 : ℝ)) (b := (40981788233 / 25000000000000 : ℝ)) (q := (1134178134681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12567])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12567]

theorem cert12568_40 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (82696455557717 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567038106419 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨40, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (82696455557717 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567038106419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_41 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (20665602743799 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268156426793 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨41, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (20665602743799 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268156426793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_42 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (82628390060991 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (226816040441 / 10000000000000 : ℝ))
      (E := (cell12568 ⟨42, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (82628390060991 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (226816040441 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_43 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (8259439278531 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268164416699 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨43, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (8259439278531 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268164416699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_44 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (8256041911851 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268168404051 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨44, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (8256041911851 / 10000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268168404051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_45 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (82526469031099 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134086212123 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨45, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (82526469031099 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134086212123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_46 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (82492542493733 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268176417191 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨46, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (82492542493733 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268176417191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_47 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (16491727895443 / 20000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567045110071 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨47, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (16491727895443 / 20000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567045110071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_48 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (5151547497031 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283523054119 / 12500000000000 : ℝ))
      (E := (cell12568 ⟨48, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (5151547497031 / 6250000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283523054119 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_49 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (82390903890673 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134094196631 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨49, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (82390903890673 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134094196631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_50 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (82357071262987 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (453638487401 / 20000000000000 : ℝ))
      (E := (cell12568 ⟨50, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (82357071262987 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (453638487401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_51 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (10290407755103 / 12500000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283524555497 / 12500000000000 : ℝ))
      (E := (cell12568 ⟨51, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (10290407755103 / 12500000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283524555497 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_52 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (642886532779 / 781250000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567050102901 / 25000000000000 : ℝ))
      (E := (cell12568 ⟨52, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (642886532779 / 781250000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (567050102901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_53 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (3290228547973 / 4000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134102227591 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨53, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (3290228547973 / 4000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134102227591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_54 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (20555493630869 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268208453731 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨54, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (20555493630869 / 25000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268208453731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_55 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (2054706466003 / 2500000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268212463133 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨55, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (2054706466003 / 2500000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268212463133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_56 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (82154566021351 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134108210467 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨56, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (82154566021351 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134108210467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_57 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (82120896639403 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268220441781 / 100000000000000 : ℝ))
      (E := (cell12568 ⟨57, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (82120896639403 / 100000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (2268220441781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_58 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (1641745009333 / 2000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134112231413 / 50000000000000 : ℝ))
      (E := (cell12568 ⟨58, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (1641745009333 / 2000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (1134112231413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12568_59 : CellCertificate 12568 (890415387006347 / 10000000000000000 : ℝ) (1671268398862773 / 1000000000000000000 : ℝ) (337674283146409 / 10000000000000000 : ℝ)
    (cell12568 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · norm_num [cell12568]
  · have h := gap_lower (n := 12568) (a := (41026813737801 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283528560013 / 12500000000000 : ℝ))
      (E := (cell12568 ⟨59, by decide⟩).energy) (xi := (337674283146409 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12568 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12568]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12568])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12568) (a := (41026813737801 / 50000000000000 : ℝ)) (b := (81956973343 / 50000000000000 : ℝ)) (q := (283528560013 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12568])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12568]

theorem cert12569_40 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82696452770323 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268024634451 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨40, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82696452770323 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268024634451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_41 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41331204247683 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567007155759 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨41, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41331204247683 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567007155759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_42 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82628387888301 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268032588821 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨42, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82628387888301 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268032588821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_43 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (16518878183867 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268036589979 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨43, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (16518878183867 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268036589979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_44 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82560417558827 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (35438134777 / 1562500000000 : ℝ))
      (E := (cell12569 ⟨44, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82560417558827 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (35438134777 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_45 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41263233888643 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567011159053 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨45, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41263233888643 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567011159053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_46 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (10311567693171 / 12500000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134024310073 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨46, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (10311567693171 / 12500000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134024310073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_47 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82458638833877 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567013158731 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨47, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82458638833877 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567013158731 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_48 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (16484951922753 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268056619973 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨48, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (16484951922753 / 20000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268056619973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_49 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82390903856129 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134030316153 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨49, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82390903856129 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134030316153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_50 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82357071532211 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (18144516887 / 800000000000 : ℝ))
      (E := (cell12569 ⟨50, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82357071532211 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (18144516887 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_51 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (41161631306699 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268068612313 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨51, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (41161631306699 / 50000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268068612313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_52 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82289477071219 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134036317059 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨52, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82289477071219 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134036317059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_53 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82255714877349 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268076614533 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨53, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82255714877349 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268076614533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_54 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (205554940009 / 250000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567020167173 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨54, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (205554940009 / 250000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567020167173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_55 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (10273532552741 / 12500000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453616935071 / 20000000000000 : ℝ))
      (E := (cell12569 ⟨55, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (10273532552741 / 12500000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (453616935071 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_56 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (8215456810443 / 10000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567022157777 / 25000000000000 : ℝ))
      (E := (cell12569 ⟨56, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (8215456810443 / 10000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (567022157777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_57 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82120899023339 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268092650597 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨57, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82120899023339 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268092650597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_58 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (8208725315103 / 10000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134048335487 / 50000000000000 : ℝ))
      (E := (cell12569 ⟨58, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (8208725315103 / 10000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (1134048335487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12569_59 : CellCertificate 12569 (445193442989987 / 5000000000000000 : ℝ) (835567693598677 / 500000000000000000 : ℝ) (1318932601713 / 39062500000000 : ℝ)
    (cell12569 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · norm_num [cell12569]
  · have h := gap_lower (n := 12569) (a := (82053630460013 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268100688273 / 100000000000000 : ℝ))
      (E := (cell12569 ⟨59, by decide⟩).energy) (xi := (1318932601713 / 39062500000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12569 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12569]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12569])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12569) (a := (82053630460013 / 100000000000000 : ℝ)) (b := (81950371293 / 50000000000000 : ℝ)) (q := (2268100688273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12569])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12569]

theorem cert12570_40 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (16539289996767 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267896839931 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨40, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (16539289996767 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267896839931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_41 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (16532481203281 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (113395043739 / 5000000000000 : ℝ))
      (E := (cell12570 ⟨41, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (16532481203281 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (113395043739 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_42 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41314192858221 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133952443789 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨42, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41314192858221 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133952443789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_43 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41297194527077 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226790887769 / 10000000000000 : ℝ))
      (E := (cell12570 ⟨43, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41297194527077 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226790887769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_44 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41280207999951 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133956422131 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨44, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41280207999951 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133956422131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_45 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (82526466524193 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (90716673803 / 4000000000000 : ℝ))
      (E := (cell12570 ⟨45, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (82526466524193 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (90716673803 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_46 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (16498508119537 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267920878911 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨46, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (16498508119537 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267920878911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_47 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (5153664886949 / 6250000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (453584977087 / 20000000000000 : ℝ))
      (E := (cell12570 ⟨47, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (5153664886949 / 6250000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (453584977087 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_48 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (82424759275641 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (141745553933 / 6250000000000 : ℝ))
      (E := (cell12570 ⟨48, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (82424759275641 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (141745553933 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_49 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (16478180764431 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (5669832171 / 250000000000 : ℝ))
      (E := (cell12570 ⟨49, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (16478180764431 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (5669832171 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_50 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (5147316987623 / 6250000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267936899773 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨50, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (5147316987623 / 6250000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267936899773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_51 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (20580815796617 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267940895763 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨51, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (20580815796617 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267940895763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_52 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (16457895589437 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267944912813 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨52, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (16457895589437 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267944912813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_53 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (41127858027897 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133974444583 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨53, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (41127858027897 / 50000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133974444583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_54 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (20555494371027 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566988220223 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨54, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (20555494371027 / 25000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566988220223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_55 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (16437652440817 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133978442427 / 50000000000000 : ℝ))
      (E := (cell12570 ⟨55, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (16437652440817 / 20000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (1133978442427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_56 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (4107728509391 / 5000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566990224427 / 25000000000000 : ℝ))
      (E := (cell12570 ⟨56, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (4107728509391 / 5000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (566990224427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_57 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (82120901407549 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (22679649159 / 1000000000000 : ℝ))
      (E := (cell12570 ⟨57, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (82120901407549 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (22679649159 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_58 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (82087255835647 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226796893567 / 10000000000000 : ℝ))
      (E := (cell12570 ⟨58, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (82087255835647 / 100000000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (226796893567 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12570_59 : CellCertificate 12570 (178071677862439 / 2000000000000000 : ℝ) (417750599175579 / 250000000000000000 : ℝ) (21101200843543 / 625000000000000 : ℝ)
    (cell12570 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · norm_num [cell12570]
  · have h := gap_lower (n := 12570) (a := (656429067557 / 800000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267972893869 / 100000000000000 : ℝ))
      (E := (cell12570 ⟨59, by decide⟩).energy) (xi := (21101200843543 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12570 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12570]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12570])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12570) (a := (656429067557 / 800000000000 : ℝ)) (b := (20485942579 / 12500000000000 : ℝ)) (q := (2267972893869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12570])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12570]

theorem cert12571_40 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (16539289439651 / 20000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133884579793 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨40, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (16539289439651 / 20000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133884579793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_41 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41331201769157 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267773182027 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨41, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41331201769157 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267773182027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_42 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (10328547943177 / 12500000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566944295779 / 25000000000000 : ℝ))
      (E := (cell12571 ⟨42, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (10328547943177 / 12500000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566944295779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_43 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (10324298398721 / 12500000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267781162221 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨43, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (10324298398721 / 12500000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267781162221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_44 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82560414441733 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267785177313 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨44, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82560414441733 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267785177313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_45 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82526465271819 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (113389458427 / 5000000000000 : ℝ))
      (E := (cell12571 ⟨45, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82526465271819 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (113389458427 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_46 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (20623134912671 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (141737074593 / 6250000000000 : ℝ))
      (E := (cell12571 ⟨46, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (20623134912671 / 25000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (141737074593 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_47 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (5153664846821 / 6250000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (113389859591 / 5000000000000 : ℝ))
      (E := (cell12571 ⟨47, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (5153664846821 / 6250000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (113389859591 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_48 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (131879614301 / 160000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267801161817 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨48, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (131879614301 / 160000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267801161817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_49 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82390903788751 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (226780516049 / 10000000000000 : ℝ))
      (E := (cell12571 ⟨49, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82390903788751 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (226780516049 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_50 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41178536036129 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (14173807411 / 625000000000 : ℝ))
      (E := (cell12571 ⟨50, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41178536036129 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (14173807411 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_51 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41161631880017 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267813176339 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨51, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41161631880017 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267813176339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_52 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (8228947882361 / 10000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (35434643573 / 1562500000000 : ℝ))
      (E := (cell12571 ⟨52, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (8228947882361 / 10000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (35434643573 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_53 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82255717234661 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267821220043 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨53, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82255717234661 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267821220043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_54 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41110989482501 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (113391260423 / 5000000000000 : ℝ))
      (E := (cell12571 ⟨54, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41110989482501 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (113391260423 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_55 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (82188263986589 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267829209807 / 100000000000000 : ℝ))
      (E := (cell12571 ⟨55, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (82188263986589 / 100000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (2267829209807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_56 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41077286135761 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133916610367 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨56, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41077286135761 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133916610367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_57 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41060451896017 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566959309423 / 25000000000000 : ℝ))
      (E := (cell12571 ⟨57, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41060451896017 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (566959309423 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_58 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41043629260251 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133920598879 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨58, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41043629260251 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133920598879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12571_59 : CellCertificate 12571 (890329897001961 / 10000000000000000 : ℝ) (417717356843151 / 250000000000000000 : ℝ) (337591685519643 / 10000000000000000 : ℝ)
    (cell12571 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · norm_num [cell12571]
  · have h := gap_lower (n := 12571) (a := (41026818214719 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133922607629 / 50000000000000 : ℝ))
      (E := (cell12571 ⟨59, by decide⟩).energy) (xi := (337591685519643 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12571 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12571]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12571])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12571) (a := (41026818214719 / 50000000000000 : ℝ)) (b := (163874340823 / 100000000000000 : ℝ)) (q := (1133922607629 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12571])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12571]

theorem cert12572_40 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82696444413581 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566910368987 / 25000000000000 : ℝ))
      (E := (cell12572 ⟨40, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82696444413581 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566910368987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_41 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (20665600265273 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133822743009 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨41, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (20665600265273 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133822743009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_42 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (4131419068761 / 5000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133824767111 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨42, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (4131419068761 / 5000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133824767111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_43 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (2581074541443 / 3125000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (113382675119 / 5000000000000 : ℝ))
      (E := (cell12572 ⟨43, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (2581074541443 / 3125000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (113382675119 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_44 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82560412884321 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133828753613 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨44, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82560412884321 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133828753613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_45 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (20631616005041 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453532297781 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨45, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (20631616005041 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453532297781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_46 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (16498507740873 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133832752501 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨46, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (16498507740873 / 20000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133832752501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_47 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82458636907731 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267669495181 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨47, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82458636907731 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267669495181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_48 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (160985856643 / 195312500000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566918379161 / 25000000000000 : ℝ))
      (E := (cell12572 ⟨48, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (160985856643 / 195312500000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566918379161 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_49 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82390903755917 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (113383875429 / 5000000000000 : ℝ))
      (E := (cell12572 ⟨49, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82390903755917 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (113383875429 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_50 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82357072343081 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133840763903 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨50, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82357072343081 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133840763903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_51 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (5145204020881 / 6250000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267685513037 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨51, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (5145204020881 / 6250000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267685513037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_52 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41144739850247 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453537904143 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨52, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41144739850247 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453537904143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_53 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82255718413949 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566923387031 / 25000000000000 : ℝ))
      (E := (cell12572 ⟨53, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82255718413949 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (566923387031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_54 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82221980446279 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267697533271 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨54, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82221980446279 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267697533271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_55 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41094132884721 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133850766019 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨55, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41094132884721 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133850766019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_56 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41077287177767 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133852770539 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨56, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41077287177767 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133852770539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_57 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (82120906176793 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133854778419 / 50000000000000 : ℝ))
      (E := (cell12572 ⟨57, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (82120906176793 / 100000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (1133854778419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_58 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (41043630602797 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453542715111 / 20000000000000 : ℝ))
      (E := (cell12572 ⟨58, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (41043630602797 / 50000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (453542715111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12572_59 : CellCertificate 12572 (35612056361929 / 400000000000000 : ℝ) (835368239601583 / 500000000000000000 : ℝ) (67512832421229 / 2000000000000000 : ℝ)
    (cell12572 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · norm_num [cell12572]
  · have h := gap_lower (n := 12572) (a := (20513409853613 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267717534077 / 100000000000000 : ℝ))
      (E := (cell12572 ⟨59, by decide⟩).energy) (xi := (67512832421229 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12572 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12572]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12572])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12572) (a := (20513409853613 / 25000000000000 : ℝ)) (b := (81930571579 / 50000000000000 : ℝ)) (q := (2267717534077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12572])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12572]

theorem cert12573_40 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (41348220814907 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267513906487 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨40, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (41348220814907 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267513906487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_41 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82662398584739 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267517904273 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨41, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82662398584739 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267517904273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_42 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82628379205857 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (226752188211 / 10000000000000 : ℝ))
      (E := (cell12573 ⟨42, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82628379205857 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (226752188211 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_43 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (41297191731689 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267525898167 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨43, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (41297191731689 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267525898167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_44 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (16512082265533 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566882473207 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨44, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (16512082265533 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566882473207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_45 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (20631615692307 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133766961937 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨45, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (20631615692307 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133766961937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_46 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (10311567219841 / 12500000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267537872329 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨46, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (10311567219841 / 12500000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267537872329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_47 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82458636266971 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133770956659 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨47, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82458636266971 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133770956659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_48 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82424758264913 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267545927409 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨48, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82424758264913 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267545927409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_49 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82390903723653 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566887478167 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨49, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82390903723653 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566887478167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_50 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (20589268153609 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267553925913 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨50, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (20589268153609 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267553925913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_51 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82323264908653 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267557905857 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨51, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82323264908653 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267557905857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_52 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (16457896115567 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133780954471 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨52, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (16457896115567 / 20000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133780954471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_53 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82255719593659 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267565932449 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨53, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82255719593659 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267565932449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_54 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (41110990963971 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566892478597 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨54, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (41110990963971 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566892478597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_55 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (41094133776321 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267573910637 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨55, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (41094133776321 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267573910637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_56 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (82154576439857 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566894479463 / 25000000000000 : ℝ))
      (E := (cell12573 ⟨56, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (82154576439857 / 100000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (566894479463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_57 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (41060454280913 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133790966237 / 50000000000000 : ℝ))
      (E := (cell12573 ⟨57, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (41060454280913 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (1133790966237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_58 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (20521815972731 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (283448243843 / 12500000000000 : ℝ))
      (E := (cell12573 ⟨58, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (20521815972731 / 25000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (283448243843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12573_59 : CellCertificate 12573 (44513646272497 / 500000000000000 : ℝ) (1670603552188951 / 1000000000000000000 : ℝ) (168768321627473 / 5000000000000000 : ℝ)
    (cell12573 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · norm_num [cell12573]
  · have h := gap_lower (n := 12573) (a := (41026821199833 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267589968691 / 100000000000000 : ℝ))
      (E := (cell12573 ⟨59, by decide⟩).energy) (xi := (168768321627473 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12573 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12573]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12573])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12573) (a := (41026821199833 / 50000000000000 : ℝ)) (b := (163847947637 / 100000000000000 : ℝ)) (q := (2267589968691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12573])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12573]

theorem cert12574_40 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41348219423477 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133693166867 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨40, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41348219423477 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133693166867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_41 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (16532479221851 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (90695612771 / 4000000000000 : ℝ))
      (E := (cell12574 ⟨41, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (16532479221851 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (90695612771 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_42 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (20657094259331 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267394285567 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨42, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (20657094259331 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267394285567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_43 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82594381601373 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267398290779 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨43, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82594381601373 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267398290779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_44 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (16512081954353 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267402334123 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨44, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (16512081954353 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267402334123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_45 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82526461519011 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267406296891 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨45, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82526461519011 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267406296891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_46 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (20623134203443 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (141713143467 / 6250000000000 : ℝ))
      (E := (cell12574 ⟨46, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (20623134203443 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (141713143467 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_47 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (16491727125371 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267414328431 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨47, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (16491727125371 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267414328431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_48 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82424757929217 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (226741833519 / 10000000000000 : ℝ))
      (E := (cell12574 ⟨48, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82424757929217 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (226741833519 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_49 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (41195451845979 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (226742231381 / 10000000000000 : ℝ))
      (E := (cell12574 ⟨49, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (41195451845979 / 50000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (226742231381 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_50 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (20589268221581 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (283428290139 / 12500000000000 : ℝ))
      (E := (cell12574 ⟨50, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (20589268221581 / 25000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (283428290139 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_51 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (16464653096741 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267430354801 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨51, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (16464653096741 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267430354801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_52 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (16457896291127 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267434353353 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨52, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (16457896291127 / 20000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267434353353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_53 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (8225572077379 / 10000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267438373021 / 100000000000000 : ℝ))
      (E := (cell12574 ⟨53, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (8225572077379 / 10000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (2267438373021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_54 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82221983409989 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566860587953 / 25000000000000 : ℝ))
      (E := (cell12574 ⟨54, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82221983409989 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (566860587953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_55 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82188269336189 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133723172803 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨55, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82188269336189 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133723172803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_56 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82154578524491 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (453490070211 / 20000000000000 : ℝ))
      (E := (cell12574 ⟨56, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82154578524491 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (453490070211 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_57 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82120910947133 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133727182301 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨57, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82120910947133 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133727182301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_58 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82087266576491 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133729191243 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨58, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82087266576491 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133729191243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

theorem cert12574_59 : CellCertificate 12574 (44512222310303 / 500000000000000 : ℝ) (167047064632491 / 100000000000000000 : ℝ) (337509128964801 / 10000000000000000 : ℝ)
    (cell12574 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · norm_num [cell12574]
  · have h := gap_lower (n := 12574) (a := (82053645385081 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133731170777 / 50000000000000 : ℝ))
      (E := (cell12574 ⟨59, by decide⟩).energy) (xi := (337509128964801 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12574 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12574]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12574])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12574) (a := (82053645385081 / 100000000000000 : ℝ)) (b := (163834754259 / 100000000000000 : ℝ)) (q := (1133731170777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12574])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12574]

end BstLean.Part268
