import BstLean.Part268CellShard12Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12650_20 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41690814966309 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564432509609 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨20, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41690814966309 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564432509609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_21 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83347131290501 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257734052213 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨21, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83347131290501 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257734052213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_22 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83312656909551 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257738067537 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨22, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83312656909551 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257738067537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_23 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20819551689211 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451548417653 / 20000000000000 : ℝ))
      (E := (cell12650 ⟨23, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20819551689211 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451548417653 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_24 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83243780799621 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (282218257457 / 12500000000000 : ℝ))
      (E := (cell12650 ⟨24, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83243780799621 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (282218257457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_25 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41604689502647 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451550008683 / 20000000000000 : ℝ))
      (E := (cell12650 ⟨25, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41604689502647 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451550008683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_26 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41587500670721 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257754042697 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨26, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41587500670721 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257754042697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_27 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83140647775809 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257758060419 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨27, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83140647775809 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257758060419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_28 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41553159138153 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (282220255101 / 12500000000000 : ℝ))
      (E := (cell12650 ⟨28, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41553159138153 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (282220255101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_29 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83072012811007 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257766044731 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨29, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83072012811007 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257766044731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_30 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83037731348149 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564442518603 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨30, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83037731348149 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564442518603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_31 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20750868464033 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128887036657 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨31, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20750868464033 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128887036657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_32 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20742310075879 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128889050843 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨32, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20742310075879 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128889050843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_33 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82935030659023 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128891051243 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨33, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82935030659023 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128891051243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_34 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20725211222883 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451557215391 / 20000000000000 : ℝ))
      (E := (cell12650 ⟨34, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20725211222883 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451557215391 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_35 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82866682970083 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (282223760591 / 12500000000000 : ℝ))
      (E := (cell12650 ⟨35, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82866682970083 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (282223760591 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_36 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (8283254486387 / 10000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257794068017 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨36, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (8283254486387 / 10000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257794068017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_37 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41399215271123 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128899043029 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨37, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41399215271123 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128899043029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_38 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82764339974719 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564450520141 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨38, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82764339974719 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564450520141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_39 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (82730273130949 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257806110373 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨39, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (82730273130949 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257806110373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12651_20 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (4169081051961 / 5000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128802789243 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨20, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (4169081051961 / 5000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128802789243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_21 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (83347122710179 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (141100598131 / 6250000000000 : ℝ))
      (E := (cell12651 ⟨21, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (83347122710179 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (141100598131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_22 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (83312648641869 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (451522712793 / 20000000000000 : ℝ))
      (E := (cell12651 ⟨22, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (83312648641869 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (451522712793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_23 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (16655639760273 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (45152351279 / 2000000000000 : ℝ))
      (E := (cell12651 ⟨23, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (16655639760273 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (45152351279 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_24 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (83243773155911 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128810786837 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨24, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (83243773155911 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128810786837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_25 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (83209371672919 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564406384533 / 25000000000000 : ℝ))
      (E := (cell12651 ⟨25, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (83209371672919 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564406384533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_26 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (2599218572499 / 3125000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257629577237 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨26, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (2599218572499 / 3125000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257629577237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_27 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (20785160266201 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257633577099 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨27, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (20785160266201 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257633577099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_28 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (41553155937669 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (451527508067 / 20000000000000 : ℝ))
      (E := (cell12651 ⟨28, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (41553155937669 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (451527508067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_29 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (16614401343929 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (282205198287 / 12500000000000 : ℝ))
      (E := (cell12651 ⟨29, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (16614401343929 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (282205198287 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_30 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (20759431391491 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257645541751 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨30, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (20759431391491 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257645541751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_31 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (41501734191347 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564412396037 / 25000000000000 : ℝ))
      (E := (cell12651 ⟨31, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (41501734191347 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564412396037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_32 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82969235138397 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257653598211 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨32, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82969235138397 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257653598211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_33 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (20733756450449 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (451531517081 / 20000000000000 : ℝ))
      (E := (cell12651 ⟨33, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (20733756450449 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (451531517081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_34 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (8290084034177 / 10000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564415401393 / 25000000000000 : ℝ))
      (E := (cell12651 ⟨34, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (8290084034177 / 10000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564415401393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_35 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (258958371023 / 312500000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257665601167 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨35, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (258958371023 / 312500000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257665601167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_36 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82832540927761 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128834786489 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨36, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82832540927761 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128834786489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_37 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82798426912327 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257673580241 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨37, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82798426912327 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257673580241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_38 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (41382168325283 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257677564669 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨38, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (41382168325283 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257677564669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_39 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (82730270112141 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128840792549 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨39, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (82730270112141 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128840792549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12652_20 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83381612147459 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (45149622291 / 2000000000000 : ℝ))
      (E := (cell12652 ⟨20, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83381612147459 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (45149622291 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_21 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (5087104134 / 6103515625 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (17636602219 / 781250000000 : ℝ))
      (E := (cell12652 ⟨21, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (5087104134 / 6103515625 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (17636602219 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_22 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (20828160093937 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564372278701 / 25000000000000 : ℝ))
      (E := (cell12652 ⟨22, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (20828160093937 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564372278701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_23 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (8327819084741 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257493094107 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨23, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (8327819084741 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257493094107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_24 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41621882756843 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257497083861 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨24, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41621882756843 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257497083861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_25 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83209364341991 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257501087449 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨25, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83209364341991 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257501087449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_26 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83174987299903 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (282188138503 / 12500000000000 : ℝ))
      (E := (cell12652 ⟨26, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83174987299903 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (282188138503 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_27 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (8314063435517 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (451501818013 / 20000000000000 : ℝ))
      (E := (cell12652 ⟨27, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (8314063435517 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (451501818013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_28 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (10388288184463 / 12500000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128756547323 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨28, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (10388288184463 / 12500000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128756547323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_29 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (4153600031479 / 5000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257517124223 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨29, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (4153600031479 / 5000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257517124223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_30 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83037719785037 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564380280627 / 25000000000000 : ℝ))
      (E := (cell12652 ⟨30, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83037719785037 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564380280627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_31 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83003462910477 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128762545711 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨31, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83003462910477 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128762545711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_32 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41484614987231 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128764545607 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨32, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41484614987231 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128764545607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_33 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (16587004189143 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257533123419 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨33, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (16587004189143 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257533123419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_34 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (82900835793117 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257537130743 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨34, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (82900835793117 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257537130743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_35 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (20716668621427 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257541114199 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨35, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (20716668621427 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257541114199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_36 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (82832536992687 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257545133219 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨36, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (82832536992687 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257545133219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_37 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41399211641703 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (451509825953 / 20000000000000 : ℝ))
      (E := (cell12652 ⟨37, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41399211641703 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (451509825953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_38 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41382166663687 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257553104177 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨38, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41382166663687 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257553104177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_39 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (16546053418851 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (282194639411 / 12500000000000 : ℝ))
      (E := (cell12652 ⟨39, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (16546053418851 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (282194639411 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12653_20 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (10422700407167 / 12500000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (70542395207 / 3125000000000 : ℝ))
      (E := (cell12653 ⟨20, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (10422700407167 / 12500000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (70542395207 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_21 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83347105554333 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128680326157 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨21, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83347105554333 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128680326157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_22 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83312632111189 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (564341165433 / 25000000000000 : ℝ))
      (E := (cell12653 ⟨22, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83312632111189 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (564341165433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_23 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41639091447489 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257368678737 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨23, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41639091447489 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257368678737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_24 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83243757872947 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128686324291 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨24, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83243757872947 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128686324291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_25 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (8320935701251 / 10000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128688345681 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨25, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (8320935701251 / 10000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128688345681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_26 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (2599218133789 / 3125000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257380693469 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨26, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (2599218133789 / 3125000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257380693469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_27 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83140627646909 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (9029538631 / 400000000000 : ℝ))
      (E := (cell12653 ⟨27, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83140627646909 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (9029538631 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_28 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (20776574769351 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128694351871 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨28, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (20776574769351 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128694351871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_29 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83071994540811 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (225739265851 / 10000000000000 : ℝ))
      (E := (cell12653 ⟨29, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83071994540811 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (225739265851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_30 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83037714005369 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257396699663 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨30, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83037714005369 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257396699663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_31 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41501728719741 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (70543770427 / 3125000000000 : ℝ))
      (E := (cell12653 ⟨31, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41501728719741 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (70543770427 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_32 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82969224811711 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257404697803 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨32, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82969224811711 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257404697803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_33 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (4146750804539 / 5000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257408657947 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨33, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (4146750804539 / 5000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257408657947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_34 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (20725207811393 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257412711071 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨34, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (20725207811393 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257412711071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_35 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (10358333780641 / 12500000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257416682447 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨35, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (10358333780641 / 12500000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257416682447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_36 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41416266529323 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (225742069009 / 10000000000000 : ℝ))
      (E := (cell12653 ⟨36, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41416266529323 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (225742069009 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_37 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82798419655481 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128712337979 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨37, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82798419655481 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128712337979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_38 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (82764330005141 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257428699087 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨38, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (82764330005141 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257428699087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_39 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (20682566019323 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (112871635047 / 5000000000000 : ℝ))
      (E := (cell12653 ⟨39, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (20682566019323 / 25000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (112871635047 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12654_20 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (1667631887377 / 2000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (112861614563 / 5000000000000 : ℝ))
      (E := (cell12654 ⟨20, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (1667631887377 / 2000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (112861614563 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_21 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (8334709697881 / 10000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451447254989 / 20000000000000 : ℝ))
      (E := (cell12654 ⟨21, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (8334709697881 / 10000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451447254989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_22 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (8331262384819 / 10000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257240263073 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨22, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (8331262384819 / 10000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257240263073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_23 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83278174944069 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128622129749 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨23, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83278174944069 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128622129749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_24 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83243750233693 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (7053900837 / 312500000000 : ℝ))
      (E := (cell12654 ⟨24, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83243750233693 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (7053900837 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_25 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83209349684477 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257252291483 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨25, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83209349684477 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257252291483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_26 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83174973264003 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128628137581 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨26, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83174973264003 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128628137581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_27 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41570310470009 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128630140081 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨27, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41570310470009 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128630140081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_28 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83106292680437 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257264309163 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨28, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83106292680437 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257264309163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_29 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41535994226669 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564317076533 / 25000000000000 : ℝ))
      (E := (cell12654 ⟨29, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41535994226669 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564317076533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_30 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (1037971352837 / 1250000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257272273221 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨30, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (1037971352837 / 1250000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257272273221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_31 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83003451969707 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (14107976693 / 625000000000 : ℝ))
      (E := (cell12654 ⟨31, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83003451969707 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (14107976693 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_32 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41484609825071 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (282160037609 / 12500000000000 : ℝ))
      (E := (cell12654 ⟨32, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41484609825071 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (282160037609 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_33 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82935011236991 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257284306151 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨33, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82935011236991 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257284306151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_34 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (647662708587 / 781250000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257288287953 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨34, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (647662708587 / 781250000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257288287953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_35 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82866666005619 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451458461183 / 20000000000000 : ℝ))
      (E := (cell12654 ⟨35, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82866666005619 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451458461183 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_36 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82832529125639 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128648151121 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨36, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82832529125639 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128648151121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_37 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (10349802003569 / 12500000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257300336167 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨37, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (10349802003569 / 12500000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257300336167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_38 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (82764326683867 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128652145353 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨38, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (82764326683867 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128652145353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_39 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (66184208849 / 80000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257308342061 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨39, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (66184208849 / 80000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257308342061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12655_20 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (83381585482001 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257107931909 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨20, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (83381585482001 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257107931909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_21 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20836772101221 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257111951929 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨21, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20836772101221 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257111951929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_22 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (1301759618543 / 1562500000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564278979707 / 25000000000000 : ℝ))
      (E := (cell12655 ⟨22, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (1301759618543 / 1562500000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564278979707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_23 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (83278166994683 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257119953079 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨23, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (83278166994683 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257119953079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_24 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20810935648981 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564280985409 / 25000000000000 : ℝ))
      (E := (cell12655 ⟨24, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20810935648981 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564280985409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_25 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (8320934235789 / 10000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451425589241 / 20000000000000 : ℝ))
      (E := (cell12655 ⟨25, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (8320934235789 / 10000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451425589241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_26 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (41587483124083 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128565955759 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨26, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (41587483124083 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128565955759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_27 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (83140614234499 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257135957297 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨27, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (83140614234499 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257135957297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_28 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20776571571201 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564284977727 / 25000000000000 : ℝ))
      (E := (cell12655 ⟨28, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20776571571201 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564284977727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_29 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (2076799559179 / 2500000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128571975059 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨29, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (2076799559179 / 2500000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128571975059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_30 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (5189856403113 / 6250000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128573980099 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨30, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (5189856403113 / 6250000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128573980099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_31 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (2593857703161 / 3125000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257151943069 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨31, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (2593857703161 / 3125000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257151943069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_32 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20742303622439 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (35268061859 / 1562500000000 : ℝ))
      (E := (cell12655 ⟨32, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20742303622439 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (35268061859 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_33 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (82935006384347 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257159950873 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨33, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (82935006384347 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257159950873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_34 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (82900822153807 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564290979999 / 25000000000000 : ℝ))
      (E := (cell12655 ⟨34, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (82900822153807 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564290979999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_35 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (4143333088359 / 5000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257167925979 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨35, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (4143333088359 / 5000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257167925979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_36 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (16566505038733 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257171969677 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨36, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (16566505038733 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257171969677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_37 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (82798412402619 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128587967187 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨37, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (82798412402619 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128587967187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_38 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (2586385105111 / 3125000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (225717993773 / 10000000000000 : ℝ))
      (E := (cell12655 ⟨38, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (2586385105111 / 3125000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (225717993773 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_39 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (8273025804613 / 10000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (282147997491 / 12500000000000 : ℝ))
      (E := (cell12655 ⟨39, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (8273025804613 / 10000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (282147997491 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12656_20 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83381576596789 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256983626847 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨20, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83381576596789 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256983626847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_21 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83347079832557 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128493812483 / 50000000000000 : ℝ))
      (E := (cell12656 ⟨21, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83347079832557 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128493812483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_22 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (41656303663437 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564247907249 / 25000000000000 : ℝ))
      (E := (cell12656 ⟨22, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (41656303663437 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564247907249 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_23 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83278159046819 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256995584447 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨23, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83278159046819 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256995584447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_24 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (41621867479819 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451399922321 / 20000000000000 : ℝ))
      (E := (cell12656 ⟨24, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (41621867479819 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451399922321 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_25 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (332837340131 / 400000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257003597137 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨25, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (332837340131 / 400000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257003597137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_26 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83174959233737 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128503801269 / 50000000000000 : ℝ))
      (E := (cell12656 ⟨26, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83174959233737 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128503801269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_27 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (1662812150607 / 2000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (3526580673 / 156250000000 : ℝ))
      (E := (cell12656 ⟨27, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (1662812150607 / 2000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (3526580673 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_28 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (10388284986313 / 12500000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (141063476619 / 6250000000000 : ℝ))
      (E := (cell12656 ⟨28, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (10388284986313 / 12500000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (141063476619 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_29 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83071976282277 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128509824477 / 50000000000000 : ℝ))
      (E := (cell12656 ⟨29, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83071976282277 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (1128509824477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_30 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (41518848336957 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257023643579 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨30, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (41518848336957 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257023643579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_31 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83003441033817 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (22570276117 / 1000000000000 : ℝ))
      (E := (cell12656 ⟨31, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83003441033817 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (22570276117 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_32 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (82969209330553 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (56425790339 / 2500000000000 : ℝ))
      (E := (cell12656 ⟨32, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (82969209330553 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (56425790339 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_33 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (5183437595803 / 6250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564258912673 / 25000000000000 : ℝ))
      (E := (cell12656 ⟨33, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (5183437595803 / 6250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564258912673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_34 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (41450408804793 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257039607197 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨34, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (41450408804793 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257039607197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_35 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20716664382453 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257043659889 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨35, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20716664382453 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257043659889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_36 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (3313300850509 / 4000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (141065477109 / 6250000000000 : ℝ))
      (E := (cell12656 ⟨36, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (3313300850509 / 4000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (141065477109 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_37 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (41399204388841 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257051646599 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨37, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (41399204388841 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257051646599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_38 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (16552864008839 / 20000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257055640161 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨38, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (16552864008839 / 20000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257055640161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_39 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20682563757983 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257059673263 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨39, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20682563757983 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2257059673263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12657_20 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20845391928303 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (564214829451 / 25000000000000 : ℝ))
      (E := (cell12657 ⟨20, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20845391928303 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (564214829451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_21 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20836767815457 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256863352357 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨21, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20836767815457 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256863352357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_22 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20828149767139 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (112843366763 / 5000000000000 : ℝ))
      (E := (cell12657 ⟨22, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20828149767139 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (112843366763 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_23 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20819537775119 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256871328639 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨23, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20819537775119 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256871328639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_24 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20810931831209 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128437668057 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨24, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20810931831209 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128437668057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_25 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (16641865541811 / 20000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (282109920133 / 12500000000000 : ℝ))
      (E := (cell12657 ⟨25, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (16641865541811 / 20000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (282109920133 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_26 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20793738055179 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256883348223 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨26, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20793738055179 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256883348223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_27 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (83140600827571 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256887358871 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨27, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (83140600827571 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256887358871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_28 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (1298535523399 / 1562500000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256891337227 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨28, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (1298535523399 / 1562500000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256891337227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_29 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (8307197019869 / 10000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (564223836039 / 25000000000000 : ℝ))
      (E := (cell12657 ⟨29, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (8307197019869 / 10000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (564223836039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_30 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (83037690899277 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451379864673 / 20000000000000 : ℝ))
      (E := (cell12657 ⟨30, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (83037690899277 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451379864673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_31 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41501717783851 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128451667653 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨31, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41501717783851 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128451667653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_32 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (20742301043133 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128453661591 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨32, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (20742301043133 / 25000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128453661591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_33 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41467498341247 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (282113918379 / 12500000000000 : ℝ))
      (E := (cell12657 ⟨33, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41467498341247 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (282113918379 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_34 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82900813066473 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256915349559 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨34, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82900813066473 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256915349559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_35 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82866653293513 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256919331771 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨35, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82866653293513 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256919331771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_36 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (5177032333301 / 6250000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128461676549 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨36, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (5177032333301 / 6250000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128461676549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_37 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (4139920257687 / 5000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256927355497 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨37, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (4139920257687 / 5000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256927355497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_38 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (82764316725797 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256931339303 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨38, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (82764316725797 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256931339303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_39 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41365126009327 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (564233840837 / 25000000000000 : ℝ))
      (E := (cell12657 ⟨39, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41365126009327 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (564233840837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12658_20 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83381558831271 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256735063051 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨20, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83381558831271 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256735063051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_21 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (10418382836587 / 12500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (451347815161 / 20000000000000 : ℝ))
      (E := (cell12658 ⟨21, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (10418382836587 / 12500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (451347815161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_22 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41656295405899 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (112837154797 / 5000000000000 : ℝ))
      (E := (cell12658 ⟨22, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41656295405899 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (112837154797 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_23 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (16655628631131 / 20000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128373534483 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨23, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (16655628631131 / 20000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128373534483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_24 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41621859845759 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564187778791 / 25000000000000 : ℝ))
      (E := (cell12658 ⟨24, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41621859845759 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564187778791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_25 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41604660193403 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256755121203 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨25, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41604660193403 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256755121203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_26 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83174945209103 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256759090159 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨26, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83174945209103 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256759090159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_27 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83140594126163 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256763083311 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨27, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83140594126163 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256763083311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_28 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (831062671059 / 1000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256767103341 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨28, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (831062671059 / 1000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256767103341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_29 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83071964116397 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (225677109421 / 10000000000000 : ℝ))
      (E := (cell12658 ⟨29, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83071964116397 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (225677109421 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_30 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83037685125897 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128387558287 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨30, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83037685125897 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128387558287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_31 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41501715051403 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256779113889 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨31, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41501715051403 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256779113889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_32 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82969199015693 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128391543921 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨32, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82969199015693 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128391543921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_33 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (20733747958321 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (282098387309 / 12500000000000 : ℝ))
      (E := (cell12658 ⟨33, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (20733747958321 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (282098387309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_34 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41450404262233 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256791088481 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨34, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41450404262233 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256791088481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_35 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (20716662264571 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128397558751 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨35, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (20716662264571 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128397558751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_36 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (4141625670197 / 5000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256799127737 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨36, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (4141625670197 / 5000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256799127737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_37 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (82798401530793 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256803119743 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨37, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (82798401530793 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256803119743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_38 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (20691078352089 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128403546927 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨38, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (20691078352089 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128403546927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_39 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41365124503149 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128405554451 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨39, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41365124503149 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128405554451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12659_20 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (16676309990193 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256610862591 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨20, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (16676309990193 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256610862591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_21 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41673527062581 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451322982381 / 20000000000000 : ℝ))
      (E := (cell12659 ⟨21, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41673527062581 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451322982381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_22 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41656291278299 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128309455519 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨22, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41656291278299 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128309455519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_23 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41639067606177 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564155715943 / 25000000000000 : ℝ))
      (E := (cell12659 ⟨23, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41639067606177 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564155715943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_24 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (83243712059683 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564156722597 / 25000000000000 : ℝ))
      (E := (cell12659 ⟨24, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (83243712059683 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564156722597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_25 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41604656533001 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451326175511 / 20000000000000 : ℝ))
      (E := (cell12659 ⟨25, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41604656533001 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451326175511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_26 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41587469099449 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128317443381 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨26, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41587469099449 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128317443381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_27 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (83140587426123 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (56415973023 / 2500000000000 : ℝ))
      (E := (cell12659 ⟨27, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (83140587426123 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (56415973023 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_28 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (20776565178899 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (282080358223 / 12500000000000 : ℝ))
      (E := (cell12659 ⟨28, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (20776565178899 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (282080358223 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_29 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41535979017699 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128323449559 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨29, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41535979017699 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128323449559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_30 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (83037679353773 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225665090619 / 10000000000000 : ℝ))
      (E := (cell12659 ⟨30, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (83037679353773 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225665090619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_31 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (8300342463913 / 10000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564163722229 / 25000000000000 : ℝ))
      (E := (cell12659 ⟨31, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (8300342463913 / 10000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564163722229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_32 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (16593838772007 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256658907541 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨32, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (16593838772007 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256658907541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_33 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41467493492609 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256662905013 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨33, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41467493492609 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256662905013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_34 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41450401991783 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128333441283 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨34, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41450401991783 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128333441283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_35 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (662933158593 / 800000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256670899831 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨35, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (662933158593 / 800000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256670899831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_36 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82832509476097 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225667489901 / 10000000000000 : ℝ))
      (E := (cell12659 ⟨36, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82832509476097 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225667489901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_37 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (82798397908841 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451335787867 / 20000000000000 : ℝ))
      (E := (cell12659 ⟨37, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (82798397908841 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (451335787867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_38 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41382155045937 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256682903813 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨38, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41382155045937 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256682903813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_39 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41365122997431 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256686909927 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨39, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41365122997431 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256686909927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12660_20 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41690770536147 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (90259468657 / 4000000000000 : ℝ))
      (E := (cell12660 ⟨20, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41690770536147 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (90259468657 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_21 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (10418380694903 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256490744063 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨21, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (10418380694903 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256490744063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_22 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (20828143575739 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128247361117 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨22, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (20828143575739 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128247361117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_23 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (3331125090823 / 4000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256498713059 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨23, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (3331125090823 / 4000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256498713059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_24 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (8324370442933 / 10000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256502720157 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨24, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (8324370442933 / 10000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256502720157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_25 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41604652873321 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451301349381 / 20000000000000 : ℝ))
      (E := (cell12660 ⟨25, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41604652873321 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451301349381 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_26 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (83174931190099 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256510738033 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨26, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (83174931190099 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256510738033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_27 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (83140580727453 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256514696381 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨27, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (83140580727453 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256514696381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_28 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (83106254326623 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128259370741 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨28, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (83106254326623 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128259370741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_29 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (20767987988923 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451304540079 / 20000000000000 : ℝ))
      (E := (cell12660 ⟨29, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (20767987988923 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (451304540079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_30 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41518836791453 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128263375361 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨30, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41518836791453 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128263375361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_31 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (2593856849271 / 3125000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128265359461 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨31, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (2593856849271 / 3125000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128265359461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_32 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82969188705559 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564133680931 / 25000000000000 : ℝ))
      (E := (cell12660 ⟨32, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82969188705559 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564133680931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_33 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (10366872767287 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256538708077 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨33, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (10366872767287 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256538708077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_34 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (82900799443773 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256542731813 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨34, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (82900799443773 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256542731813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_35 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41433320295517 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128273368693 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨35, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41433320295517 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128273368693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_36 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (16566501109857 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564137681393 / 25000000000000 : ℝ))
      (E := (cell12660 ⟨36, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (16566501109857 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564137681393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_37 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (20699598571971 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256554755603 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨37, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (20699598571971 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256554755603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_38 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (20691076694087 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (70517461537 / 3125000000000 : ℝ))
      (E := (cell12660 ⟨38, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (20691076694087 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (70517461537 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_39 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41365121492173 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (282070345803 / 12500000000000 : ℝ))
      (E := (cell12660 ⟨39, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41365121492173 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (282070345803 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12661_20 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (10422691524407 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128181283141 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨20, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (10422691524407 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128181283141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_21 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41673518497441 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (564091643071 / 25000000000000 : ℝ))
      (E := (cell12661 ⟨21, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41673518497441 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (564091643071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_22 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (83312566050873 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256370587851 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨22, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (83312566050873 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256370587851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_23 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16655623866063 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128187279243 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨23, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16655623866063 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128187279243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_24 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (4162184840023 / 5000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256378604471 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨24, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (4162184840023 / 5000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256378604471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_25 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (10401162303591 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256382612471 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨25, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (10401162303591 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256382612471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_26 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (83174924182707 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256386585559 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨26, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (83174924182707 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256386585559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_27 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (10392571753769 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128195292507 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨27, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (10392571753769 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128195292507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_28 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41553123969491 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282049326689 / 12500000000000 : ℝ))
      (E := (cell12661 ⟨28, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41553123969491 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282049326689 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_29 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (83071945877281 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128199307507 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨29, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (83071945877281 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128199307507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_30 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41518833906647 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (141025161979 / 6250000000000 : ℝ))
      (E := (cell12661 ⟨30, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41518833906647 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (141025161979 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_31 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (10375426714429 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256406603909 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨31, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (10375426714429 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256406603909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_32 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82969183552263 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256410594951 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨32, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82969183552263 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256410594951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_33 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41467488646259 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282051828103 / 12500000000000 : ℝ))
      (E := (cell12661 ⟨33, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41467488646259 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282051828103 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_34 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16580158981017 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256418636229 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨34, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16580158981017 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256418636229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_35 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (20716659089753 / 25000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256422630169 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨35, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (20716659089753 / 25000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256422630169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_36 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (5177031351469 / 6250000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (35256665741 / 1562500000000 : ℝ))
      (E := (cell12661 ⟨36, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (5177031351469 / 6250000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (35256665741 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_37 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82798390667921 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256430627223 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨37, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82798390667921 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256430627223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_38 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (4138215173089 / 5000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (225643463127 / 10000000000000 : ℝ))
      (E := (cell12661 ⟨38, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (4138215173089 / 5000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (225643463127 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_39 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (82730239974751 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (90257544787 / 4000000000000 : ℝ))
      (E := (cell12661 ⟨39, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (82730239974751 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (90257544787 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12662_20 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83381523319853 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256238470433 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨20, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83381523319853 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256238470433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_21 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (16669405686427 / 20000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256242513161 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨21, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (16669405686427 / 20000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256242513161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_22 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (20828139450087 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (141015406743 / 6250000000000 : ℝ))
      (E := (cell12662 ⟨22, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (20828139450087 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (141015406743 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_23 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (3331124455663 / 4000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256250516741 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨23, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (3331124455663 / 4000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256250516741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_24 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83243689173071 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128127242481 / 50000000000000 : ℝ))
      (E := (cell12662 ⟨24, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83243689173071 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128127242481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_25 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83209291112257 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256258474253 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨25, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83209291112257 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256258474253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_26 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83174917176721 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451252497551 / 20000000000000 : ℝ))
      (E := (cell12662 ⟨26, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83174917176721 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451252497551 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_27 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83140567334219 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (112813323497 / 5000000000000 : ℝ))
      (E := (cell12662 ⟨27, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83140567334219 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (112813323497 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_28 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83106241552671 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128135240937 / 50000000000000 : ℝ))
      (E := (cell12662 ⟨28, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83106241552671 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128135240937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_29 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41535969900081 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256274526003 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨29, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41535969900081 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256274526003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_30 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41518831022469 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564069621881 / 25000000000000 : ℝ))
      (E := (cell12662 ⟨30, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41518831022469 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564069621881 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_31 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (8300340825541 / 10000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (70508827667 / 3125000000000 : ℝ))
      (E := (cell12662 ⟨31, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (8300340825541 / 10000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (70508827667 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_32 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (20742294600037 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128143260609 / 50000000000000 : ℝ))
      (E := (cell12662 ⟨32, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (20742294600037 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128143260609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_33 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41467486223941 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (141018158631 / 6250000000000 : ℝ))
      (E := (cell12662 ⟨33, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41467486223941 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (141018158631 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_34 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82900790367503 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128147268603 / 50000000000000 : ℝ))
      (E := (cell12662 ⟨34, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82900790367503 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128147268603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_35 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82866632128059 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2203416523 / 97656250000 : ℝ))
      (E := (cell12662 ⟨35, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82866632128059 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2203416523 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_36 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (16566499539751 / 20000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564075636141 / 25000000000000 : ℝ))
      (E := (cell12662 ⟨36, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (16566499539751 / 20000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564075636141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_37 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (10349798381119 / 12500000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256306495519 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨37, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (10349798381119 / 12500000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256306495519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_38 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (82764300148169 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (70509704649 / 3125000000000 : ℝ))
      (E := (cell12662 ⟨38, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (82764300148169 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (70509704649 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_39 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (3309209478643 / 4000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256314528399 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨39, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (3309209478643 / 4000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256314528399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12663_20 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (83381514446083 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256114428883 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨20, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (83381514446083 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256114428883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_21 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (10418377483873 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256118450099 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨21, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (10418377483873 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256118450099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_22 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (4165627477569 / 5000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256122424027 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨22, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (4165627477569 / 5000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256122424027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_23 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (16655620690871 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (225612641279 / 10000000000000 : ℝ))
      (E := (cell12663 ⟨23, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (16655620690871 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (225612641279 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_24 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (20810920386791 / 25000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256130420001 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨24, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (20810920386791 / 25000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256130420001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_25 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (83209283797229 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256134449037 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨25, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (83209283797229 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256134449037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_26 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (83174910172141 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256138444623 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨26, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (83174910172141 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256138444623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_27 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41570280319827 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256142468039 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨27, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41570280319827 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256142468039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_28 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (83106235167691 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128073231747 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨28, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (83106235167691 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128073231747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_29 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (5191995857771 / 6250000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451230086673 / 20000000000000 : ℝ))
      (E := (cell12663 ⟨29, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (5191995857771 / 6250000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451230086673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_30 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (83037656277837 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (70504826197 / 3125000000000 : ℝ))
      (E := (cell12663 ⟨30, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (83037656277837 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (70504826197 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_31 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41501701398303 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1762623767 / 78125000000 : ℝ))
      (E := (cell12663 ⟨31, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41501701398303 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1762623767 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_32 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82969173249213 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128081221987 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨32, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82969173249213 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128081221987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_33 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82934967604389 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128083223947 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨33, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82934967604389 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128083223947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_34 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82900785831027 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256170434747 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨34, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82900785831027 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256170434747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_35 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41433313949087 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451234892833 / 20000000000000 : ℝ))
      (E := (cell12663 ⟨35, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41433313949087 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451234892833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_36 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (20708123443759 / 25000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128089239173 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨36, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (20708123443759 / 25000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128089239173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_37 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82798383430977 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256182477841 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨37, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82798383430977 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256182477841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_38 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41382148417757 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256186462983 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨38, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41382148417757 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256186462983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_39 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (82730233958319 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256190492599 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨39, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (82730233958319 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256190492599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12664_20 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83381505573947 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (563997595839 / 25000000000000 : ℝ))
      (E := (cell12664 ⟨20, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83381505573947 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (563997595839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_21 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83347011311429 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (22559943831 / 1000000000000 : ℝ))
      (E := (cell12664 ⟨21, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83347011311429 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (22559943831 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_22 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83312541303969 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255998394589 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨22, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83312541303969 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255998394589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_23 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41639047759327 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (225600242167 / 10000000000000 : ℝ))
      (E := (cell12664 ⟨23, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41639047759327 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (225600242167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_24 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41621836961369 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564001602397 / 25000000000000 : ℝ))
      (E := (cell12664 ⟨24, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41621836961369 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564001602397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_25 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (16641855296729 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256010420039 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨25, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (16641855296729 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256010420039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_26 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41587451584483 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256014397749 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨26, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41587451584483 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256014397749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_27 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83140553946457 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128009201997 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨27, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83140553946457 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128009201997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_28 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83106228784041 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256022441449 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨28, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83106228784041 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256022441449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_29 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41535963824901 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256026395587 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨29, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41535963824901 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256026395587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_30 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83037650511991 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (451206088801 / 20000000000000 : ℝ))
      (E := (cell12664 ⟨30, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83037650511991 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (451206088801 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_31 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83003397339019 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256034413159 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨31, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83003397339019 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256034413159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_32 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82969168099457 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (90241536871 / 4000000000000 : ℝ))
      (E := (cell12664 ⟨32, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82969168099457 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (90241536871 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_33 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82934962762039 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128021206399 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨33, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82934962762039 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128021206399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_34 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (16580156259131 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256046446061 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨34, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (16580156259131 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256046446061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_35 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (20716655917339 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (282006308001 / 12500000000000 : ℝ))
      (E := (cell12664 ⟨35, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (20716655917339 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (282006308001 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_36 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (82832489852349 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256054467417 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨36, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (82832489852349 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2256054467417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_37 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (20699594953499 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128029228421 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨37, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (20699594953499 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128029228421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_38 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (10345536690477 / 12500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564015608153 / 25000000000000 : ℝ))
      (E := (cell12664 ⟨38, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (10345536690477 / 12500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (564015608153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_39 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41365115475741 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128033226777 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨39, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41365115475741 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1128033226777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12665_20 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83381496703443 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563966612601 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨20, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83381496703443 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563966612601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_21 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83347002753467 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255870428763 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨21, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83347002753467 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255870428763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_22 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41656266529057 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281984302447 / 12500000000000 : ℝ))
      (E := (cell12665 ⟨22, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41656266529057 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281984302447 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_23 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83278087584471 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255878426693 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨23, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83278087584471 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255878426693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_24 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (5202729143737 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (90235298149 / 4000000000000 : ℝ))
      (E := (cell12665 ⟨24, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (5202729143737 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (90235298149 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_25 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (5200579323219 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255886445653 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨25, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (5200579323219 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255886445653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_26 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (20793724041799 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563972601387 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨26, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (20793724041799 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563972601387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_27 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83140547254627 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (28875449 / 1280000000 : ℝ))
      (E := (cell12665 ⟨27, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83140547254627 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (28875449 / 1280000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_28 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (2077655560043 / 2500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (112794920787 / 5000000000000 : ℝ))
      (E := (cell12665 ⟨28, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (2077655560043 / 2500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (112794920787 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_29 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83071921576561 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255902412667 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨29, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83071921576561 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255902412667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_30 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (415188223737 / 500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127953223059 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨30, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (415188223737 / 500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127953223059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_31 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83003391882649 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127955229771 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨31, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83003391882649 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127955229771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_32 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41484581475441 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255914454621 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨32, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41484581475441 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255914454621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_33 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82934957920831 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (225591843281 / 10000000000000 : ℝ))
      (E := (cell12665 ⟨33, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82934957920831 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (225591843281 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_34 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82900776761389 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255922453939 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨34, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82900776761389 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255922453939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_35 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41433309720803 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (451185292091 / 20000000000000 : ℝ))
      (E := (cell12665 ⟨35, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41433309720803 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (451185292091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_36 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82832485930691 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255930453133 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨36, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82832485930691 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255930453133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_37 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82798376198007 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (90237377301 / 4000000000000 : ℝ))
      (E := (cell12665 ⟨37, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82798376198007 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (90237377301 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_38 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (82764290213073 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127969228829 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨38, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (82764290213073 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127969228829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_39 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (20682556986391 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127971234993 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨39, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (20682556986391 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127971234993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12666_20 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83381487834571 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563935613801 / 25000000000000 : ℝ))
      (E := (cell12666 ⟨20, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83381487834571 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563935613801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_21 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (833469941971 / 1000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225574647049 / 10000000000000 : ℝ))
      (E := (cell12666 ⟨21, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (833469941971 / 1000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225574647049 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_22 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (10414065601727 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255750498989 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨22, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (10414065601727 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255750498989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_23 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (41639039825903 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563938621551 / 25000000000000 : ℝ))
      (E := (cell12666 ⟨23, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (41639039825903 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563938621551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_24 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83243658678327 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255758494043 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨24, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83243658678327 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255758494043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_25 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (16641852372161 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255762467487 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨25, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (16641852372161 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255762467487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_26 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83174889166831 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255766468023 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨26, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83174889166831 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255766468023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_27 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (16628108112833 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127885249277 / 50000000000000 : ℝ))
      (E := (cell12666 ⟨27, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (16628108112833 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127885249277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_28 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83106216020729 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563943625823 / 25000000000000 : ℝ))
      (E := (cell12666 ⟨28, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83106216020729 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563943625823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_29 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83071915504611 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225577848461 / 10000000000000 : ℝ))
      (E := (cell12666 ⟨29, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83071915504611 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225577848461 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_30 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83037638984063 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (451156500631 / 20000000000000 : ℝ))
      (E := (cell12666 ⟨30, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83037638984063 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (451156500631 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_31 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (10375423303437 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255786502377 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨31, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (10375423303437 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255786502377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_32 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (16593831560697 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127895241979 / 50000000000000 : ℝ))
      (E := (cell12666 ⟨32, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (16593831560697 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127895241979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_33 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (16586990616153 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225579450793 / 10000000000000 : ℝ))
      (E := (cell12666 ⟨33, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (16586990616153 / 20000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225579450793 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_34 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82900772228227 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255798516989 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨34, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82900772228227 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255798516989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_35 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (20716653803731 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255802512133 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨35, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (20716653803731 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255802512133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_36 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (5177030125629 / 6250000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255806494141 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨36, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (5177030125629 / 6250000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255806494141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_37 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (82798372583011 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563952630559 / 25000000000000 : ℝ))
      (E := (cell12666 ⟨37, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (82798372583011 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563952630559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_38 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (41382143451643 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (56395363453 / 2500000000000 : ℝ))
      (E := (cell12666 ⟨38, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (41382143451643 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (56395363453 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_39 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (20682556235141 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255818541897 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨39, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (20682556235141 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255818541897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12667_20 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83381478967331 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255618572581 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨20, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83381478967331 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255618572581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_21 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83346985642327 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127811283291 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨21, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83346985642327 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127811283291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_22 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83312516571073 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563906643627 / 25000000000000 : ℝ))
      (E := (cell12667 ⟨22, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83312516571073 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563906643627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_23 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83278071720659 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (112781527093 / 5000000000000 : ℝ))
      (E := (cell12667 ⟨23, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83278071720659 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (112781527093 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_24 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (41621825529171 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127817294457 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨24, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (41621825529171 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127817294457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_25 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20802313637887 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (35244352249 / 1562500000000 : ℝ))
      (E := (cell12667 ⟨25, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20802313637887 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (35244352249 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_26 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83174882167871 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255642585173 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨26, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83174882167871 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255642585173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_27 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20785133468767 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127823299361 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨27, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20785133468767 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127823299361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_28 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (41553104820533 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255650587183 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨28, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (41553104820533 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255650587183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_29 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83071909433953 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (70489204779 / 3125000000000 : ℝ))
      (E := (cell12667 ⟨29, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83071909433953 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (70489204779 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_30 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83037633221979 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255658556607 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨30, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83037633221979 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255658556607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_31 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83003380973559 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255662600199 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨31, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83003380973559 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255662600199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_32 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20742288164317 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127833284171 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨32, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20742288164317 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127833284171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_33 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (1036686853023 / 1250000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255670579581 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨33, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (1036686853023 / 1250000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255670579581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_34 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82900767696169 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127837288303 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨34, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82900767696169 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127837288303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_35 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20716652747327 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127839309523 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨35, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20716652747327 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127839309523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_36 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (41416239045233 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563920647611 / 25000000000000 : ℝ))
      (E := (cell12667 ⟨36, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (41416239045233 / 50000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563920647611 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_37 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (5174898060563 / 6250000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (225568660863 / 10000000000000 : ℝ))
      (E := (cell12667 ⟨37, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (5174898060563 / 6250000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (225568660863 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_38 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (16552856718891 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127845307651 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨38, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (16552856718891 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127845307651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_39 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (82730221936483 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127847305283 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨39, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (82730221936483 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127847305283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12668_20 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41690735050861 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563873671497 / 25000000000000 : ℝ))
      (E := (cell12668 ⟨20, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41690735050861 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563873671497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_21 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41673488544573 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127749358521 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨21, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41673488544573 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127749358521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_22 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41656254164943 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (281937838057 / 12500000000000 : ℝ))
      (E := (cell12668 ⟨22, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41656254164943 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (281937838057 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_23 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (8327806379103 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (140969169397 / 6250000000000 : ℝ))
      (E := (cell12668 ⟨23, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (8327806379103 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (140969169397 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_24 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83243643439837 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (70484708749 / 3125000000000 : ℝ))
      (E := (cell12668 ⟨24, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83243643439837 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (70484708749 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_25 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83209247243733 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255514675001 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨25, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83209247243733 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255514675001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_26 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41587437585157 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127759349293 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨26, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41587437585157 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127759349293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_27 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83140527187339 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255522695189 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨27, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83140527187339 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255522695189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_28 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83106203262733 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (18044213807 / 800000000000 : ℝ))
      (E := (cell12668 ⟨28, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83106203262733 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (18044213807 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_29 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (16614380672917 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255530676111 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨29, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (16614380672917 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255530676111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_30 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83037627461149 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127767361747 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨30, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83037627461149 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127767361747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_31 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41501687760419 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563884673619 / 25000000000000 : ℝ))
      (E := (cell12668 ⟨31, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41501687760419 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563884673619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_32 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82969147512229 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255542707777 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨32, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82969147512229 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255542707777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_33 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (10366867925507 / 12500000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255546706343 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨33, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (10366867925507 / 12500000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255546706343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_34 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (16580152633043 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255550691397 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨34, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (16580152633043 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255550691397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_35 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82866606764759 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127777361283 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨35, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82866606764759 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127777361283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_36 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82832474171897 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (451111748409 / 20000000000000 : ℝ))
      (E := (cell12668 ⟨36, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82832474171897 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (451111748409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_37 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82798365355997 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127781375191 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨37, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82798365355997 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127781375191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_38 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (82764280286579 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (451113349581 / 20000000000000 : ℝ))
      (E := (cell12668 ⟨38, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (82764280286579 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (451113349581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_39 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (2068255473333 / 2500000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563892683679 / 25000000000000 : ℝ))
      (E := (cell12668 ⟨39, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (2068255473333 / 2500000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (563892683679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12669_20 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (5211341327359 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255370853699 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨20, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (5211341327359 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255370853699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_21 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83346968537559 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (140960928973 / 6250000000000 : ℝ))
      (E := (cell12669 ⟨21, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83346968537559 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (140960928973 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_22 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41656250045127 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225537883051 / 10000000000000 : ℝ))
      (E := (cell12669 ⟨22, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41656250045127 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225537883051 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_23 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83278055862917 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225538287499 / 10000000000000 : ℝ))
      (E := (cell12669 ⟨23, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83278055862917 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225538287499 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_24 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (8324363582281 / 10000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127693441973 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨24, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (8324363582281 / 10000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127693441973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_25 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (1040115499217 / 1250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255390860681 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨25, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (1040115499217 / 1250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255390860681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_26 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83174868174161 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563848716669 / 25000000000000 : ℝ))
      (E := (cell12669 ⟨26, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83174868174161 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563848716669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_27 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (3325620820039 / 4000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255398846397 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨27, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (3325620820039 / 4000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255398846397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_28 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83106196885727 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255402860907 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨28, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83106196885727 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255402860907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_29 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (20767974324127 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127703427079 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨29, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (20767974324127 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127703427079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_30 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (20759405425393 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127705443399 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨30, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (20759405425393 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127705443399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_31 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83003370069333 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255414843739 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨31, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83003370069333 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255414843739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_32 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (5185571398023 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (451083768741 / 20000000000000 : ℝ))
      (E := (cell12669 ⟨32, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (5185571398023 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (451083768741 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_33 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41467469283707 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (451084577643 / 20000000000000 : ℝ))
      (E := (cell12669 ⟨33, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41467469283707 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (451084577643 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_34 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (16580151727073 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (28192835767 / 1250000000000 : ℝ))
      (E := (cell12669 ⟨34, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (16580151727073 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (28192835767 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_35 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (20716650635319 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255430881321 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨35, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (20716650635319 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255430881321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_36 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41416235127179 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225543489029 / 10000000000000 : ℝ))
      (E := (cell12669 ⟨36, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41416235127179 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225543489029 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_37 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41399180871989 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255438888817 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨37, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41399180871989 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255438888817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_38 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41382138489829 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563860719307 / 25000000000000 : ℝ))
      (E := (cell12669 ⟨38, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41382138489829 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563860719307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_39 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (3309208637243 / 4000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255446914347 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨39, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (3309208637243 / 4000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255446914347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12670_20 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83381452375397 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451049415143 / 20000000000000 : ℝ))
      (E := (cell12670 ⟨20, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83381452375397 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451049415143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_21 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (16669391997513 / 20000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255251064463 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨21, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (16669391997513 / 20000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255251064463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_22 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (5207030740761 / 6250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127627534659 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨22, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (5207030740761 / 6250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127627534659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_23 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41639023968161 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (90210361431 / 4000000000000 : ℝ))
      (E := (cell12670 ⟨23, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41639023968161 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (90210361431 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_24 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83243628207263 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255263025741 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨24, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83243628207263 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255263025741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_25 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83209232632427 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255267042587 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨25, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83209232632427 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255267042587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_26 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83174861179411 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255271031031 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨26, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83174861179411 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255271031031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_27 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (10392564226997 / 12500000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563818763087 / 25000000000000 : ℝ))
      (E := (cell12670 ⟨27, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (10392564226997 / 12500000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563818763087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_28 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83106190510049 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255279050743 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨28, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83106190510049 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255279050743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_29 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41535945614861 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255283087071 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨29, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41535945614861 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255283087071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_30 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (5189850996453 / 6250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (56382176163 / 2500000000000 : ℝ))
      (E := (cell12670 ⟨30, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (5189850996453 / 6250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (56382176163 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_31 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83003364619043 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127645523997 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨31, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83003364619043 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127645523997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_32 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41484568612843 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (56382377331 / 2500000000000 : ℝ))
      (E := (cell12670 ⟨32, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41484568612843 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (56382377331 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_33 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (10366866716489 / 12500000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127649533311 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨33, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (10366866716489 / 12500000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127649533311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_34 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41450377053309 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255303086499 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨34, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41450377053309 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255303086499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_35 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (4143329915943 / 5000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (140956693457 / 6250000000000 : ℝ))
      (E := (cell12670 ⟨35, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (4143329915943 / 5000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (140956693457 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_36 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (10354058292231 / 12500000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127655546917 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨36, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (10354058292231 / 12500000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127655546917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_37 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (82798358132951 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563828770653 / 25000000000000 : ℝ))
      (E := (cell12670 ⟨37, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (82798358132951 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563828770653 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_38 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (20691068418423 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563829765493 / 25000000000000 : ℝ))
      (E := (cell12670 ⟨38, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (20691068418423 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563829765493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_39 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (20682553232437 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255323090739 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨39, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (20682553232437 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255323090739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12671_20 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (2084536087867 / 2500000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255123293763 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨20, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (2084536087867 / 2500000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255123293763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_21 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41673475719581 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255127261429 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨21, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41673475719581 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255127261429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_22 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (20828120903913 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451026260847 / 20000000000000 : ℝ))
      (E := (cell12671 ⟨22, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (20828120903913 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451026260847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_23 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41639020005621 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (11275676547 / 500000000000 : ℝ))
      (E := (cell12671 ⟨23, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41639020005621 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (11275676547 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_24 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83243620593193 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255139280461 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨24, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83243620593193 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255139280461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_25 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (16641845065787 / 20000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (225514327911 / 10000000000000 : ℝ))
      (E := (cell12671 ⟨25, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (16641845065787 / 20000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (225514327911 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_26 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (5198428386629 / 6250000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127573654241 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨26, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (5198428386629 / 6250000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127573654241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_27 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83140507132343 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (28189391413 / 1250000000000 : ℝ))
      (E := (cell12671 ⟨27, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83140507132343 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (28189391413 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_28 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83106184135699 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255155295383 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨28, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83106184135699 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255155295383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_29 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41535942582113 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255159316363 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨29, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41535942582113 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255159316363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_30 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (1297462659159 / 1562500000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255163319679 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨30, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (1297462659159 / 1562500000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255163319679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_31 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83003359169969 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563791826809 / 25000000000000 : ℝ))
      (E := (cell12671 ⟨31, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83003359169969 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563791826809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_32 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (4148456604209 / 5000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451034256143 / 20000000000000 : ℝ))
      (E := (cell12671 ⟨32, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (4148456604209 / 5000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451034256143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_33 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (1658698577951 / 2000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127587650071 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨33, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (1658698577951 / 2000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127587650071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_34 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41450374789487 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255179308209 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨34, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41450374789487 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255179308209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_35 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (82866594097509 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255183305913 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨35, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (82866594097509 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255183305913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_36 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41416231211183 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (90207491761 / 4000000000000 : ℝ))
      (E := (cell12671 ⟨36, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41416231211183 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (90207491761 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_37 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (16559670904583 / 20000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255191331767 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨37, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (16559670904583 / 20000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255191331767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_38 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (2069106759217 / 2500000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127597651069 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨38, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (2069106759217 / 2500000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127597651069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_39 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41365104964669 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255199322613 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨39, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41365104964669 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255199322613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12672_20 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (10422679331949 / 12500000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (56374989153 / 2500000000000 : ℝ))
      (E := (cell12672 ⟨20, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (10422679331949 / 12500000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (56374989153 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_21 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83346942892351 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (451000714213 / 20000000000000 : ℝ))
      (E := (cell12672 ⟨21, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83346942892351 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (451000714213 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_22 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41656237690341 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127503767631 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨22, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41656237690341 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127503767631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_23 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83278032087679 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127505789587 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨23, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83278032087679 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127505789587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_24 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41621806490301 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255015531369 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨24, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41621806490301 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255015531369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_25 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83209218026883 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127509785127 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨25, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83209218026883 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127509785127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_26 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (2079371179853 / 2500000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255023582199 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨26, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (2079371179853 / 2500000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255023582199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_27 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41570250225037 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255027570037 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨27, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41570250225037 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255027570037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_28 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83106177762677 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (451006307273 / 20000000000000 : ℝ))
      (E := (cell12672 ⟨28, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83106177762677 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (451006307273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_29 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83071879100019 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255035542037 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨29, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83071879100019 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255035542037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_30 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83037604430357 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255039589259 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨30, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83037604430357 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255039589259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_31 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83003353722109 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255043562939 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨31, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83003353722109 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255043562939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_32 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82969126943853 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127523790899 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨32, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82969126943853 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127523790899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_33 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (10366865508041 / 12500000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255051588777 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨33, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (10366865508041 / 12500000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255051588777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_34 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82900745052433 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (281881948137 / 12500000000000 : ℝ))
      (E := (cell12672 ⟨34, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82900745052433 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (281881948137 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_35 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82866589877223 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255059571753 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨35, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82866589877223 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255059571753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_36 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (82832458507913 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255063608167 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨36, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (82832458507913 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255063608167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_37 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (8279835091387 / 10000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (225506757761 / 10000000000000 : ℝ))
      (E := (cell12672 ⟨37, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (8279835091387 / 10000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (225506757761 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_38 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41382133532311 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (70470987429 / 3125000000000 : ℝ))
      (E := (cell12672 ⟨38, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41382133532311 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (70470987429 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_39 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (16546041385969 / 20000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255075609973 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨39, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (16546041385969 / 20000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2255075609973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12673_20 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41690712899067 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254875834511 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨20, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41690712899067 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254875834511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_21 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (20836733586783 / 25000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127439938387 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨21, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (20836733586783 / 25000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127439938387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_22 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41656233573633 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254883879047 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨22, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41656233573633 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254883879047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_23 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (8327802416563 / 10000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254887845101 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨23, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (8327802416563 / 10000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254887845101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_24 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83243605369489 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254891836837 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨24, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83243605369489 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254891836837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_25 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83209210726271 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127447928813 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨25, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83209210726271 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127447928813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_26 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83174840203577 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (281862481523 / 12500000000000 : ℝ))
      (E := (cell12673 ⟨26, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83174840203577 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (281862481523 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_27 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83140493769171 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (112745194089 / 5000000000000 : ℝ))
      (E := (cell12673 ⟨27, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83140493769171 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (112745194089 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_28 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83106171390981 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254907890619 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨28, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83106171390981 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254907890619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_29 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83071873037101 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254911881069 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨29, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83071873037101 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254911881069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_30 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83037598675789 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254915855261 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨30, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83037598675789 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254915855261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_31 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83003348275463 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450983974727 / 20000000000000 : ℝ))
      (E := (cell12673 ⟨31, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83003348275463 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450983974727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_32 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41484560902351 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127461939691 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨32, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41484560902351 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127461939691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_33 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41467459616123 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254927873949 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨33, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41467459616123 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254927873949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_34 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41450370263497 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127465929279 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨34, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41450370263497 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127465929279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_35 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82866585658003 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254935892833 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨35, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82866585658003 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254935892833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_36 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82832454594487 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (225493986031 / 10000000000000 : ℝ))
      (E := (cell12673 ⟨36, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82832454594487 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (225493986031 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_37 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82798347305817 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (70466996213 / 3125000000000 : ℝ))
      (E := (cell12673 ⟨37, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82798347305817 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (70466996213 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_38 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82764263761517 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450989578009 / 20000000000000 : ℝ))
      (E := (cell12673 ⟨38, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82764263761517 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450989578009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_39 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (82730203931269 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254951894097 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨39, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (82730203931269 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254951894097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12674_20 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (16676283388461 / 20000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254752215487 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨20, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (16676283388461 / 20000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254752215487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_21 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83346925803503 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563689044639 / 25000000000000 : ℝ))
      (E := (cell12674 ⟨21, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83346925803503 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563689044639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_22 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (41656229457701 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (35230628421 / 1562500000000 : ℝ))
      (E := (cell12674 ⟨22, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (41656229457701 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (35230628421 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_23 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83278016245097 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (225476422387 / 10000000000000 : ℝ))
      (E := (cell12674 ⟨23, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83278016245097 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (225476422387 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_24 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (20810899439963 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (8807688269 / 390625000000 : ℝ))
      (E := (cell12674 ⟨24, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (20810899439963 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (8807688269 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_25 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83209203427099 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254772199619 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨25, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83209203427099 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254772199619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_26 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83174833214437 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (45095523537 / 2000000000000 : ℝ))
      (E := (cell12674 ⟨26, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83174833214437 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (45095523537 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_27 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83140487089631 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254780189827 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨27, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83140487089631 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254780189827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_28 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83106165020611 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127392091377 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨28, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83106165020611 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127392091377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_29 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83071866975473 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254788216481 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨29, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83071866975473 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254788216481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_30 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83037592922473 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254792234703 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨30, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83037592922473 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254792234703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_31 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83003342830031 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563699059831 / 25000000000000 : ℝ))
      (E := (cell12674 ⟨31, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83003342830031 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563699059831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_32 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (10371139583341 / 12500000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254800232019 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨32, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (10371139583341 / 12500000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254800232019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_33 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82934914401303 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254804214237 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨33, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82934914401303 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254804214237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_34 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82900736002657 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127404122901 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨34, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82900736002657 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127404122901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_35 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82866581439847 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (90192488421 / 4000000000000 : ℝ))
      (E := (cell12674 ⟨35, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82866581439847 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (90192488421 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_36 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82832450682089 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450963245281 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨36, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82832450682089 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450963245281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_37 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82798343698753 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450964047077 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨37, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82798343698753 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450964047077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_38 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82764260459367 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450964847557 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨38, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82764260459367 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450964847557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_39 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (82730200933609 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254828233707 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨39, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (82730200933609 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254828233707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

end BstLean.Part268
