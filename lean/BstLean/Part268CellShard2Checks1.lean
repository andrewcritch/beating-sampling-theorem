import BstLean.Part268CellShard2Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12400_20 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (83383905794873 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145112041227 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨20, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (83383905794873 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145112041227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_21 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (1302333244773 / 1562500000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290228090769 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨21, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (1302333244773 / 1562500000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290228090769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_22 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41657386954127 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (572558022439 / 25000000000000 : ℝ))
      (E := (cell12400 ⟨22, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41657386954127 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (572558022439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_23 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (83280244490067 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290236083699 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨23, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (83280244490067 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290236083699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_24 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41622869688967 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458048015329 / 20000000000000 : ℝ))
      (E := (cell12400 ⟨24, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41622869688967 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458048015329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_25 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (16642251707809 / 20000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290244072403 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨25, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (16642251707809 / 20000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290244072403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_26 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41588400970381 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458049614909 / 20000000000000 : ℝ))
      (E := (cell12400 ⟨26, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41588400970381 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (458049614909 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_27 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (83142369550611 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286281510801 / 12500000000000 : ℝ))
      (E := (cell12400 ⟨27, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (83142369550611 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (286281510801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_28 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (2597123791759 / 3125000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290256052661 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨28, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (2597123791759 / 3125000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290256052661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_29 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (20768394316413 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145130017281 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨29, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (20768394316413 / 25000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145130017281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_30 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (83039217306729 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290264034749 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨30, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (83039217306729 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290264034749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_31 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (83004881427707 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290268055629 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨31, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (83004881427707 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290268055629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_32 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (10371321199617 / 12500000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (45805440817 / 2000000000000 : ℝ))
      (E := (cell12400 ⟨32, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (10371321199617 / 12500000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (45805440817 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_33 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82936281782931 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290276050839 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨33, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82936281782931 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290276050839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_34 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82902017954363 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290280028741 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨34, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82902017954363 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290280028741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_35 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41433889040033 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (91611361383 / 4000000000000 : ℝ))
      (E := (cell12400 ⟨35, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41433889040033 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (91611361383 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_36 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (10354195266129 / 12500000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145144034803 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨36, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (10354195266129 / 12500000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145144034803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_37 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (82799370070409 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290292017579 / 100000000000000 : ℝ))
      (E := (cell12400 ⟨37, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (82799370070409 / 100000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (2290292017579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_38 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (16553040374701 / 20000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145148027589 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨38, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (16553040374701 / 20000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145148027589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12400_39 : CellCertificate 12400 (89526628869941 / 1000000000000000 : ℝ) (846959507493821 / 500000000000000000 : ℝ) (342366361558549 / 10000000000000000 : ℝ)
    (cell12400 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · norm_num [cell12400]
  · have h := gap_lower (n := 12400) (a := (41365528753891 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145150003491 / 50000000000000 : ℝ))
      (E := (cell12400 ⟨39, by decide⟩).energy) (xi := (342366361558549 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12400 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12400]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12400])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12400) (a := (41365528753891 / 50000000000000 : ℝ)) (b := (83081572037 / 50000000000000 : ℝ)) (q := (1145150003491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12400])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12400]

theorem cert12401_20 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41691948239273 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572521930489 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨20, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41691948239273 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572521930489 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_21 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (20837329668003 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290091751137 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨21, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (20837329668003 / 25000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290091751137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_22 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83314765237207 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290095713469 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨22, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83314765237207 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290095713469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_23 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (16656047228197 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290099729801 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨23, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (16656047228197 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290099729801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_24 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41622865675183 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572525936477 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨24, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41622865675183 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572525936477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_25 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83211250832543 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (71565865851 / 3125000000000 : ℝ))
      (E := (cell12401 ⟨25, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83211250832543 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (71565865851 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_26 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41588397277439 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290111734051 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨26, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41588397277439 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290111734051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_27 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83142362484899 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572528928237 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨27, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83142362484899 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572528928237 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_28 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (831079545903 / 1000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145059852697 / 50000000000000 : ℝ))
      (E := (cell12401 ⟨28, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (831079545903 / 1000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145059852697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_29 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (16614714167789 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145061857127 / 50000000000000 : ℝ))
      (E := (cell12401 ⟨29, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (16614714167789 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1145061857127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_30 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (83039211198857 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (458025536737 / 20000000000000 : ℝ))
      (E := (cell12401 ⟨30, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (83039211198857 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (458025536737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_31 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41502437819113 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290131674529 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨31, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41502437819113 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290131674529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_32 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (16594112825081 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1789168507 / 78125000000 : ℝ))
      (E := (cell12401 ⟨32, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (16594112825081 / 20000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (1789168507 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_33 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82936276628907 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572534917593 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨33, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82936276628907 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572534917593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_34 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (41451006558703 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572535919747 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨34, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (41451006558703 / 50000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572535919747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_35 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (10358471694967 / 12500000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (22901477163 / 1000000000000 : ℝ))
      (E := (cell12401 ⟨35, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (10358471694967 / 12500000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (22901477163 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_36 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (82833557924889 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290151666323 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨36, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (82833557924889 / 100000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290151666323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_37 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (646870048297 / 781250000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290155705897 / 100000000000000 : ℝ))
      (E := (cell12401 ⟨37, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (646870048297 / 781250000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (2290155705897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_38 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (10345649787553 / 12500000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572539914973 / 25000000000000 : ℝ))
      (E := (cell12401 ⟨38, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (10345649787553 / 12500000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (572539914973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12401_39 : CellCertificate 12401 (895237040277497 / 10000000000000000 : ℝ) (1693782373637301 / 1000000000000000000 : ℝ) (68467607829719 / 2000000000000000 : ℝ)
    (cell12401 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · norm_num [cell12401]
  · have h := gap_lower (n := 12401) (a := (3309242169983 / 4000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (57254092621 / 2500000000000 : ℝ))
      (E := (cell12401 ⟨39, by decide⟩).energy) (xi := (68467607829719 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12401 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12401]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12401])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12401) (a := (3309242169983 / 4000000000000 : ℝ)) (b := (166149571527 / 100000000000000 : ℝ)) (q := (57254092621 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12401])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12401]

theorem cert12402_20 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (16676777432793 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (17890245433 / 781250000000 : ℝ))
      (E := (cell12402 ⟨20, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (16676777432793 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (17890245433 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_21 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83349309680257 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (457991093107 / 20000000000000 : ℝ))
      (E := (cell12402 ⟨21, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83349309680257 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (457991093107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_22 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83314756567827 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (228995944957 / 10000000000000 : ℝ))
      (E := (cell12402 ⟨22, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83314756567827 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (228995944957 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_23 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83280227793529 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (114498171503 / 5000000000000 : ℝ))
      (E := (cell12402 ⟨23, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83280227793529 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (114498171503 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_24 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (16649144664877 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (45799348221 / 2000000000000 : ℝ))
      (E := (cell12402 ⟨24, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (16649144664877 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (45799348221 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_25 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (20802810781897 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144985698173 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨25, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (20802810781897 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144985698173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_26 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83176787170501 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289975447907 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨26, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83176787170501 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289975447907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_27 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (20785588855163 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144989696953 / 50000000000000 : ℝ))
      (E := (cell12402 ⟨27, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (20785588855163 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (1144989696953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_28 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (83107947845739 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289983412607 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨28, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (83107947845739 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289983412607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_29 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (10384195551703 / 12500000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (143124211877 / 6250000000000 : ℝ))
      (E := (cell12402 ⟨29, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (10384195551703 / 12500000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (143124211877 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_30 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (20759801273083 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289991387231 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨30, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (20759801273083 / 25000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289991387231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_31 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (41502434925027 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289995406607 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨31, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (41502434925027 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289995406607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_32 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82970558655143 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289999391807 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨32, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82970558655143 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2289999391807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_33 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82936271476113 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290003403257 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨33, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82936271476113 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290003403257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_34 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82902008281639 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (22900073841 / 1000000000000 : ℝ))
      (E := (cell12402 ⟨34, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82902008281639 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (22900073841 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_35 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82867769040557 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (143125712147 / 6250000000000 : ℝ))
      (E := (cell12402 ⟨35, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82867769040557 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (143125712147 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_36 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (41416776860929 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (143125961041 / 6250000000000 : ℝ))
      (E := (cell12402 ⟨36, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (41416776860929 / 50000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (143125961041 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_37 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (16559872458939 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290019390623 / 100000000000000 : ℝ))
      (E := (cell12402 ⟨37, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (16559872458939 / 20000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (2290019390623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_38 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (662121557827 / 800000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572505844599 / 25000000000000 : ℝ))
      (E := (cell12402 ⟨38, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (662121557827 / 800000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572505844599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12402_39 : CellCertificate 12402 (447603898197571 / 5000000000000000 : ℝ) (6774583017319 / 4000000000000000 : ℝ) (68461944304621 / 2000000000000000 : ℝ)
    (cell12402 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · norm_num [cell12402]
  · have h := gap_lower (n := 12402) (a := (82731050992361 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572506849797 / 25000000000000 : ℝ))
      (E := (cell12402 ⟨39, by decide⟩).energy) (xi := (68461944304621 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12402 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12402]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12402])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12402) (a := (82731050992361 / 100000000000000 : ℝ)) (b := (83068000611 / 50000000000000 : ℝ)) (q := (572506849797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12402])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12402]

theorem cert12403_20 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83383877851131 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457963044221 / 20000000000000 : ℝ))
      (E := (cell12403 ⟨20, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83383877851131 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (457963044221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_21 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (2604665646569 / 3125000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (572454808491 / 25000000000000 : ℝ))
      (E := (cell12403 ⟨21, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (2604665646569 / 3125000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (572454808491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_22 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83314747900113 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289823181473 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨22, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83314747900113 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289823181473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_23 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (41640109723849 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289827184481 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨23, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (41640109723849 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289827184481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_24 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83245715299989 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (57245779719 / 2500000000000 : ℝ))
      (E := (cell12403 ⟨24, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83245715299989 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (57245779719 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_25 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (41605617712089 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (572458799529 / 25000000000000 : ℝ))
      (E := (cell12403 ⟨25, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (41605617712089 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (572458799529 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_26 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83176779787629 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (57245980403 / 2500000000000 : ℝ))
      (E := (cell12403 ⟨26, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83176779787629 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (57245980403 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_27 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (5196396772367 / 6250000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289843187693 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨27, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (5196396772367 / 6250000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289843187693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_28 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (16621588220521 / 20000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289847174303 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨28, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (16621588220521 / 20000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289847174303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_29 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (8307355798969 / 10000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (35778924669 / 1562500000000 : ℝ))
      (E := (cell12403 ⟨29, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (8307355798969 / 10000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (35778924669 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_30 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (41519599493577 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (228985520387 / 10000000000000 : ℝ))
      (E := (cell12403 ⟨30, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (41519599493577 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (228985520387 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_31 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (83004864063189 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289859193361 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨31, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (83004864063189 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289859193361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_32 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82970553186149 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (143116446837 / 6250000000000 : ℝ))
      (E := (cell12403 ⟨32, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82970553186149 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (143116446837 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_33 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (20734066581137 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144933595473 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨33, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (20734066581137 / 25000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144933595473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_34 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (41451001723531 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144935572039 / 50000000000000 : ℝ))
      (E := (cell12403 ⟨34, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (41451001723531 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (1144935572039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_35 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82867764522527 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289875185937 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨35, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82867764522527 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289875185937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_36 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (41416774759969 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289879141983 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨36, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (41416774759969 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289879141983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_37 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (16559871681689 / 20000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286235391301 / 12500000000000 : ℝ))
      (E := (cell12403 ⟨37, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (16559871681689 / 20000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (286235391301 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_38 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (41382595578679 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289887152023 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨38, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (41382595578679 / 50000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289887152023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12403_39 : CellCertificate 12403 (895178557051241 / 10000000000000000 : ℝ) (1693509157059657 / 1000000000000000000 : ℝ) (13691256347229 / 400000000000000 : ℝ)
    (cell12403 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · norm_num [cell12403]
  · have h := gap_lower (n := 12403) (a := (82731047736141 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289891148721 / 100000000000000 : ℝ))
      (E := (cell12403 ⟨39, by decide⟩).energy) (xi := (13691256347229 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12403 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12403]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12403])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12403) (a := (82731047736141 / 100000000000000 : ℝ)) (b := (166122433157 / 100000000000000 : ℝ)) (q := (2289891148721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12403])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12403]

theorem cert12404_20 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41691934270021 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144839511253 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨20, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41691934270021 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144839511253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_21 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (16669858340373 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (91587322257 / 4000000000000 : ℝ))
      (E := (cell12404 ⟨21, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (16669858340373 / 20000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (91587322257 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_22 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (5207171202129 / 6250000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289687025767 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨22, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (5207171202129 / 6250000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289687025767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_23 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41640105551747 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (114484552569 / 5000000000000 : ℝ))
      (E := (cell12404 ⟨23, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41640105551747 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (114484552569 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_24 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41622853638589 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (286211877587 / 12500000000000 : ℝ))
      (E := (cell12404 ⟨24, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41622853638589 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (286211877587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_25 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41605613861157 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289698995811 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨25, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41605613861157 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289698995811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_26 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (83176772406263 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144851519343 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨26, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (83176772406263 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144851519343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_27 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41571170648279 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (22897070359 / 1000000000000 : ℝ))
      (E := (cell12404 ⟨27, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41571170648279 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (22897070359 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_28 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (83107934360897 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144855495241 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨28, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (83107934360897 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144855495241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_29 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41536775783571 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289715022149 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨29, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41536775783571 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289715022149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_30 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (83039192883323 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144859508319 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨30, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (83039192883323 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144859508319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_31 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (324237727647 / 390625000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572430744071 / 25000000000000 : ℝ))
      (E := (cell12404 ⟨31, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (324237727647 / 390625000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (572430744071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_32 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41485273859211 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289727020249 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨32, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41485273859211 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289727020249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_33 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (8293626117421 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144865487443 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨33, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (8293626117421 / 10000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144865487443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_34 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82901998613673 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144867508751 / 50000000000000 : ℝ))
      (E := (cell12404 ⟨34, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82901998613673 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (1144867508751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_35 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82867760005647 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289738973853 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨35, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82867760005647 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289738973853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_36 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82833545319127 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289742962307 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨36, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82833545319127 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289742962307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_37 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (41399677261633 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (22897469839 / 1000000000000 : ℝ))
      (E := (cell12404 ⟨37, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (41399677261633 / 50000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (22897469839 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_38 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82765187587373 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289750980773 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨38, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82765187587373 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289750980773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12404_39 : CellCertificate 12404 (179029864448937 / 2000000000000000 : ℝ) (211671572727711 / 125000000000000000 : ℝ) (171126550310051 / 5000000000000000 : ℝ)
    (cell12404 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · norm_num [cell12404]
  · have h := gap_lower (n := 12404) (a := (82731044480913 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289754953441 / 100000000000000 : ℝ))
      (E := (cell12404 ⟨39, by decide⟩).energy) (xi := (171126550310051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12404 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12404]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12404])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12404) (a := (82731044480913 / 100000000000000 : ℝ)) (b := (41527216833 / 25000000000000 : ℝ)) (q := (2289754953441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12404])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12404]

theorem cert12405_20 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41691929615349 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (18316343489 / 800000000000 : ℝ))
      (E := (cell12405 ⟨20, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41691929615349 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (18316343489 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_21 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83349282715227 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289546932919 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨21, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83349282715227 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289546932919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_22 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (1041434132121 / 1250000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289550924159 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨22, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (1041434132121 / 1250000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289550924159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_23 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83280202760913 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (18316439313 / 800000000000 : ℝ))
      (E := (cell12405 ⟨23, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83280202760913 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (18316439313 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_24 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83245699255953 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144779453429 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨24, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83245699255953 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144779453429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_25 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (16642244004399 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144781453081 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨25, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (16642244004399 / 20000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144781453081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_26 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83176765026403 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289566915607 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨26, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83176765026403 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289566915607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_27 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83142334236709 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144785440057 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨27, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83142334236709 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144785440057 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_28 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41553963810307 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289574919581 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨28, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41553963810307 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289574919581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_29 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (4153677257299 / 5000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289578920029 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨29, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (4153677257299 / 5000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289578920029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_30 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83039186780839 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144791442009 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨30, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83039186780839 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144791442009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_31 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (83004852493381 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (228958687239 / 10000000000000 : ℝ))
      (E := (cell12405 ⟨31, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (83004852493381 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (228958687239 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_32 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82970542251963 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457918177463 / 20000000000000 : ℝ))
      (E := (cell12405 ⟨32, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82970542251963 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (457918177463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_33 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82936256025101 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (286199359023 / 12500000000000 : ℝ))
      (E := (cell12405 ⟨33, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82936256025101 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (286199359023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_34 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82901993781473 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289598887217 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨34, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82901993781473 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289598887217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_35 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82867755489917 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (22896028753 / 1000000000000 : ℝ))
      (E := (cell12405 ⟨35, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82867755489917 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (22896028753 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_36 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (82833541119427 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1831685517 / 80000000000 : ℝ))
      (E := (cell12405 ⟨36, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (82833541119427 / 100000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1831685517 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_37 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41399675319579 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572402723113 / 25000000000000 : ℝ))
      (E := (cell12405 ⟨37, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41399675319579 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (572402723113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_38 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (4138259200921 / 5000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144807432323 / 50000000000000 : ℝ))
      (E := (cell12405 ⟨38, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (4138259200921 / 5000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (1144807432323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12405_39 : CellCertificate 12405 (27972502874199 / 312500000000000 : ℝ) (338647205722103 / 200000000000000000 : ℝ) (171112398669941 / 5000000000000000 : ℝ)
    (cell12405 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · norm_num [cell12405]
  · have h := gap_lower (n := 12405) (a := (41365520613339 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289618872043 / 100000000000000 : ℝ))
      (E := (cell12405 ⟨39, by decide⟩).energy) (xi := (171112398669941 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12405 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12405]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12405])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12405) (a := (41365520613339 / 50000000000000 : ℝ)) (b := (166095303747 / 100000000000000 : ℝ)) (q := (2289618872043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12405])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12405]

theorem cert12406_20 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83383849923099 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (286175855683 / 12500000000000 : ℝ))
      (E := (cell12406 ⟨20, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83383849923099 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (286175855683 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_21 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83349273730293 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (286176357931 / 12500000000000 : ℝ))
      (E := (cell12406 ⟨21, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83349273730293 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (286176357931 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_22 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (1041434023837 / 1250000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289414876651 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨22, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (1041434023837 / 1250000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289414876651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_23 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41640097209979 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289418831033 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨23, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41640097209979 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289418831033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_24 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (10405711404539 / 12500000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289422847249 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨24, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (10405711404539 / 12500000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289422847249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_25 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (4160560616161 / 5000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289426870807 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨25, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (4160560616161 / 5000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289426870807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_26 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83176757648047 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289430846887 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨26, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83176757648047 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289430846887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_27 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (3325693087133 / 4000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289434837163 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨27, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (3325693087133 / 4000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289434837163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_28 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (20776980220439 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572359711183 / 25000000000000 : ℝ))
      (E := (cell12406 ⟨28, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (20776980220439 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572359711183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_29 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (20768384681551 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144721407 / 50000000000 : ℝ))
      (E := (cell12406 ⟨29, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (20768384681551 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144721407 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_30 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (830391806797 / 1000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144723403007 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨30, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (830391806797 / 1000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144723403007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_31 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (83004846710437 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (91578032927 / 4000000000000 : ℝ))
      (E := (cell12406 ⟨31, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (83004846710437 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (91578032927 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_32 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (8297053678677 / 10000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (18315638473 / 800000000000 : ℝ))
      (E := (cell12406 ⟨32, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (8297053678677 / 10000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (18315638473 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_33 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (82936250877219 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (71545588259 / 3125000000000 : ℝ))
      (E := (cell12406 ⟨33, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (82936250877219 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (71545588259 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_34 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (82901988950461 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144731405901 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨34, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (82901988950461 / 100000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144731405901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_35 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (16573550195067 / 20000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289466831683 / 100000000000000 : ℝ))
      (E := (cell12406 ⟨35, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (16573550195067 / 20000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (2289466831683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_36 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (20708384230209 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (286183853321 / 12500000000000 : ℝ))
      (E := (cell12406 ⟨36, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (20708384230209 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (286183853321 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_37 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (2069983668903 / 2500000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144737398709 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨37, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (2069983668903 / 2500000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144737398709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_38 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (41382590225249 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572369700911 / 25000000000000 : ℝ))
      (E := (cell12406 ⟨38, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (41382590225249 / 50000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (572369700911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12406_39 : CellCertificate 12406 (179018173247837 / 2000000000000000 : ℝ) (211637437177601 / 125000000000000000 : ℝ) (171098249419357 / 5000000000000000 : ℝ)
    (cell12406 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · norm_num [cell12406]
  · have h := gap_lower (n := 12406) (a := (20682759493359 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144741393569 / 50000000000000 : ℝ))
      (E := (cell12406 ⟨39, by decide⟩).energy) (xi := (171098249419357 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12406 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12406]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12406])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12406) (a := (20682759493359 / 25000000000000 : ℝ)) (b := (166081742401 / 100000000000000 : ℝ)) (q := (1144741393569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12406])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12406]

theorem cert12407_20 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16676768123449 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (143079429189 / 6250000000000 : ℝ))
      (E := (cell12407 ⟨20, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16676768123449 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (143079429189 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_21 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83349264747063 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144637424007 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨21, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83349264747063 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144637424007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_22 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16662942649181 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572319720811 / 25000000000000 : ℝ))
      (E := (cell12407 ⟨22, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16662942649181 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572319720811 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_23 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41640093040313 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144641430213 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨23, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41640093040313 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144641430213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_24 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16649136643651 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289286841871 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨24, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16649136643651 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289286841871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_25 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83211204625989 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144645415691 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨25, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83211204625989 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144645415691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_26 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16635350054239 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144647416263 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨26, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16635350054239 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144647416263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_27 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41571160060703 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144649424317 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨27, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41571160060703 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144649424317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_28 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (20776978536081 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (143081426523 / 6250000000000 : ℝ))
      (E := (cell12407 ⟨28, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (20776978536081 / 25000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (143081426523 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_29 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41536766153907 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144653410491 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨29, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41536766153907 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144653410491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_30 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (83039174579907 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572327710277 / 25000000000000 : ℝ))
      (E := (cell12407 ⟨30, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (83039174579907 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572327710277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_31 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41502420464399 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (14308217679 / 625000000000 : ℝ))
      (E := (cell12407 ⟨31, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41502420464399 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (14308217679 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_32 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16594106264569 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (143082427763 / 6250000000000 : ℝ))
      (E := (cell12407 ⟨32, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16594106264569 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (143082427763 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_33 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16587249146113 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2861653539 / 125000000000 : ℝ))
      (E := (cell12407 ⟨33, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16587249146113 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2861653539 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_34 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82901984120637 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289326849837 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨34, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82901984120637 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289326849837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_35 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (41433873230951 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289330843001 / 100000000000000 : ℝ))
      (E := (cell12407 ⟨35, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (41433873230951 / 50000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (2289330843001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_36 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16566706544671 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572333702971 / 25000000000000 : ℝ))
      (E := (cell12407 ⟨36, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16566706544671 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (572333702971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_37 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82799342874153 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144669408047 / 50000000000000 : ℝ))
      (E := (cell12407 ⟨37, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82799342874153 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (1144669408047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_38 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (82765176883607 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (228934279777 / 10000000000000 : ℝ))
      (E := (cell12407 ⟨38, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (82765176883607 / 100000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (228934279777 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12407_39 : CellCertificate 12407 (895061645038029 / 10000000000000000 : ℝ) (846481494123621 / 500000000000000000 : ℝ) (171084102557623 / 5000000000000000 : ℝ)
    (cell12407 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · norm_num [cell12407]
  · have h := gap_lower (n := 12407) (a := (16546206944237 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (57233670403 / 2500000000000 : ℝ))
      (E := (cell12407 ⟨39, by decide⟩).energy) (xi := (171084102557623 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12407 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12407]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12407])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12407) (a := (16546206944237 / 20000000000000 : ℝ)) (b := (166068183293 / 100000000000000 : ℝ)) (q := (57233670403 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12407])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12407]

theorem cert12408_20 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41691915656567 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572283735639 / 25000000000000 : ℝ))
      (E := (cell12408 ⟨20, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41691915656567 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572283735639 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_21 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83349255765537 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289138944889 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨21, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83349255765537 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289138944889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_22 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83314704586513 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289142943939 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨22, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83314704586513 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289142943939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_23 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41640088871459 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457829388797 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨23, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41640088871459 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457829388797 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_24 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41622837600891 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457830189813 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨24, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41622837600891 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457830189813 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_25 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83211196930303 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (286144363077 / 12500000000000 : ℝ))
      (E := (cell12408 ⟨25, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83211196930303 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (286144363077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_26 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83176742895847 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289158930913 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨26, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83176742895847 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289158930913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_27 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (83142313065951 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (228916291453 / 10000000000000 : ℝ))
      (E := (cell12408 ⟨27, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (83142313065951 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (228916291453 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_28 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (20776976852079 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (228916691693 / 10000000000000 : ℝ))
      (E := (cell12408 ⟨28, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (20776976852079 / 25000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (228916691693 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_29 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (10384190736351 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289170882517 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨29, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (10384190736351 / 12500000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289170882517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_30 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (4151958424073 / 5000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144587465409 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨30, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (4151958424073 / 5000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144587465409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_31 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41502417574233 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457835777757 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨31, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41502417574233 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457835777757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_32 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (16594105172037 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144591437753 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨32, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (16594105172037 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144591437753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_33 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82936240585137 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289186892921 / 100000000000000 : ℝ))
      (E := (cell12408 ⟨33, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82936240585137 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (2289186892921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_34 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82901979292001 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144595442083 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨34, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82901979292001 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144595442083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_35 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82867741949617 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (286149363657 / 12500000000000 : ℝ))
      (E := (cell12408 ⟨35, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82867741949617 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (286149363657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_36 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82833528526983 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (91567956433 / 4000000000000 : ℝ))
      (E := (cell12408 ⟨36, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82833528526983 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (91567956433 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_37 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (16559867798651 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457840577967 / 20000000000000 : ℝ))
      (E := (cell12408 ⟨37, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (16559867798651 / 20000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (457840577967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_38 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (82765173317747 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144603452847 / 50000000000000 : ℝ))
      (E := (cell12408 ⟨38, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (82765173317747 / 100000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (1144603452847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12408_39 : CellCertificate 12408 (223758107092449 / 2500000000000000 : ℝ) (423206625271123 / 250000000000000000 : ℝ) (5345936190127 / 156250000000000 : ℝ)
    (cell12408 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · norm_num [cell12408]
  · have h := gap_lower (n := 12408) (a := (41365515734963 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572302725073 / 25000000000000 : ℝ))
      (E := (cell12408 ⟨39, by decide⟩).energy) (xi := (5345936190127 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12408 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12408]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12408])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12408) (a := (41365515734963 / 50000000000000 : ℝ)) (b := (166054626423 / 100000000000000 : ℝ)) (q := (572302725073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12408])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12408]

theorem cert12409_20 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (41691911005383 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457799814413 / 20000000000000 : ℝ))
      (E := (cell12409 ⟨20, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (41691911005383 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457799814413 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_21 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (16669849357143 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572250759383 / 25000000000000 : ℝ))
      (E := (cell12409 ⟨21, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (16669849357143 / 20000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572250759383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_22 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (5207168495549 / 6250000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289007058739 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨22, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (5207168495549 / 6250000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289007058739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_23 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83280169406833 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457802204679 / 20000000000000 : ℝ))
      (E := (cell12409 ⟨23, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83280169406833 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457802204679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_24 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (20811416796723 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (286126881519 / 12500000000000 : ℝ))
      (E := (cell12409 ⟨24, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (20811416796723 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (286126881519 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_25 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83211189236159 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (45780380643 / 2000000000000 : ℝ))
      (E := (cell12409 ⟨25, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83211189236159 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (45780380643 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_26 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83176735522003 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144511512637 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨26, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83176735522003 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144511512637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_27 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (2078557650299 / 2500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289027034853 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨27, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (2078557650299 / 2500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289027034853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_28 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (20776975168433 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289031063983 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨28, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (20776975168433 / 25000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289031063983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_29 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (41536759737593 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572258764267 / 25000000000000 : ℝ))
      (E := (cell12409 ⟨29, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (41536759737593 / 50000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572258764267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_30 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83039162384357 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144519508333 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨30, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83039162384357 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144519508333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_31 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (83004829369439 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144521501807 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨31, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (83004829369439 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144521501807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_32 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (10371315049849 / 12500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289047020081 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨32, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (10371315049849 / 12500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289047020081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_33 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (10367029430117 / 12500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289051009453 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨33, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (10367029430117 / 12500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289051009453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_34 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (10362746808069 / 12500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572263757987 / 25000000000000 : ℝ))
      (E := (cell12409 ⟨34, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (10362746808069 / 12500000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (572263757987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_35 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (1035846717981 / 1250000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (45781180609 / 2000000000000 : ℝ))
      (E := (cell12409 ⟨35, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (1035846717981 / 1250000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (45781180609 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_36 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82833524331719 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457812601229 / 20000000000000 : ℝ))
      (E := (cell12409 ⟨36, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82833524331719 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (457812601229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_37 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82799335113427 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144533509321 / 50000000000000 : ℝ))
      (E := (cell12409 ⟨37, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82799335113427 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (1144533509321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_38 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82765169752917 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289071010077 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨38, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82765169752917 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289071010077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12409_39 : CellCertificate 12409 (895003216233381 / 10000000000000000 : ℝ) (846345017963617 / 500000000000000000 : ℝ) (342111631996009 / 10000000000000000 : ℝ)
    (cell12409 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · norm_num [cell12409]
  · have h := gap_lower (n := 12409) (a := (82731028219659 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289075039657 / 100000000000000 : ℝ))
      (E := (cell12409 ⟨39, by decide⟩).energy) (xi := (342111631996009 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12409 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12409]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12409])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12409) (a := (82731028219659 / 100000000000000 : ℝ)) (b := (166041071789 / 100000000000000 : ℝ)) (q := (2289075039657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12409])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12409]

theorem cert12410_20 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83383812710141 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572215813887 / 25000000000000 : ℝ))
      (E := (cell12410 ⟨20, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83383812710141 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572215813887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_21 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (16669847561519 / 20000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144433621243 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨21, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (16669847561519 / 20000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144433621243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_22 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (41657343636359 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288871227643 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨22, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (41657343636359 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288871227643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_23 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83280161072371 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572218803823 / 25000000000000 : ℝ))
      (E := (cell12410 ⟨23, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83280161072371 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572218803823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_24 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (16649131834717 / 20000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (228887920947 / 10000000000000 : ℝ))
      (E := (cell12410 ⟨24, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (16649131834717 / 20000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (228887920947 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_25 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83211181543559 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288883213981 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨25, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83211181543559 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288883213981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_26 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (41588364074831 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144443616193 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨26, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (41588364074831 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144443616193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_27 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (10392787369929 / 12500000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144445604801 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨27, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (10392787369929 / 12500000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144445604801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_28 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83107893940571 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (228889520709 / 10000000000000 : ℝ))
      (E := (cell12410 ⟨28, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83107893940571 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (228889520709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_29 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83073513060949 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (35764050433 / 1562500000000 : ℝ))
      (E := (cell12410 ⟨29, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83073513060949 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (35764050433 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_30 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83039156288599 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144451607807 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨30, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83039156288599 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144451607807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_31 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (83004823591717 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (143056701977 / 6250000000000 : ℝ))
      (E := (cell12410 ⟨31, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (83004823591717 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (143056701977 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_32 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (10371314367333 / 12500000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288911219403 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨32, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (10371314367333 / 12500000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288911219403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_33 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82936230297961 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572228795199 / 25000000000000 : ℝ))
      (E := (cell12410 ⟨33, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82936230297961 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572228795199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_34 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82901969638289 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572229794007 / 25000000000000 : ℝ))
      (E := (cell12410 ⟨34, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82901969638289 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (572229794007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_35 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (8286773292849 / 10000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144461603291 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨35, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (8286773292849 / 10000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144461603291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_36 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (20708380034391 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288927215091 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨36, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (20708380034391 / 25000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288927215091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_37 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (82799331234669 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144465601257 / 50000000000000 : ℝ))
      (E := (cell12410 ⟨37, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (82799331234669 / 100000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (1144465601257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_38 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (41382583094559 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288935169589 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨38, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (41382583094559 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288935169589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12410_39 : CellCertificate 12410 (894974008627679 / 10000000000000000 : ℝ) (846276796385073 / 500000000000000000 : ℝ) (342083352597539 / 10000000000000000 : ℝ)
    (cell12410 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · norm_num [cell12410]
  · have h := gap_lower (n := 12410) (a := (41365512485191 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288939175521 / 100000000000000 : ℝ))
      (E := (cell12410 ⟨39, by decide⟩).energy) (xi := (342083352597539 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12410 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12410]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12410])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12410) (a := (41365512485191 / 50000000000000 : ℝ)) (b := (166027519393 / 100000000000000 : ℝ)) (q := (2288939175521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12410])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12410]

theorem cert12411_20 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83383803411259 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288727493009 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨20, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83383803411259 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288727493009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_21 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83349228831177 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572182875371 / 25000000000000 : ℝ))
      (E := (cell12411 ⟨21, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83349228831177 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (572182875371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_22 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41657339309157 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (45774710179 / 2000000000000 : ℝ))
      (E := (cell12411 ⟨22, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41657339309157 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (45774710179 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_23 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (20820038184883 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (28609243267 / 1250000000000 : ℝ))
      (E := (cell12411 ⟨23, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (20820038184883 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (28609243267 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_24 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (4162282558093 / 5000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288743479369 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨24, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (4162282558093 / 5000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288743479369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_25 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83211173852501 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (8940419727 / 390625000000 : ℝ))
      (E := (cell12411 ⟨25, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83211173852501 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (8940419727 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_26 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (10397090097353 / 12500000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288751493863 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨26, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (10397090097353 / 12500000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288751493863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_27 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (83142291908367 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (114437771939 / 5000000000000 : ℝ))
      (E := (cell12411 ⟨27, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (83142291908367 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (114437771939 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_28 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (16621577441767 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144379731563 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨28, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (16621577441767 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144379731563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_29 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (2596047082753 / 3125000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288763452913 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨29, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (2596047082753 / 3125000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288763452913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_30 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (16607830038837 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (17880995853 / 781250000000 : ℝ))
      (E := (cell12411 ⟨30, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (16607830038837 / 20000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (17880995853 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_31 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (830048178153 / 1000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288771455829 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨31, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (830048178153 / 1000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288771455829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_32 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41485254739901 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144387736737 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨32, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41485254739901 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144387736737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_33 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (20734056289053 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144389732753 / 50000000000000 : ℝ))
      (E := (cell12411 ⟨33, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (20734056289053 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (1144389732753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_34 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (41450982406607 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288783433561 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨34, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (41450982406607 / 50000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288783433561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_35 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (1294808256557 / 1562500000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457757487531 / 20000000000000 : ℝ))
      (E := (cell12411 ⟨35, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (1294808256557 / 1562500000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457757487531 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_36 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82833515944517 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288791420417 / 100000000000000 : ℝ))
      (E := (cell12411 ⟨36, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82833515944517 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (2288791420417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_37 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82799327356979 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457759088291 / 20000000000000 : ℝ))
      (E := (cell12411 ⟨37, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82799327356979 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457759088291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_38 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (20691290656587 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457759888581 / 20000000000000 : ℝ))
      (E := (cell12411 ⟨38, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (20691290656587 / 25000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (457759888581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12411_39 : CellCertificate 12411 (447472402775793 / 5000000000000000 : ℝ) (169241717160791 / 100000000000000000 : ℝ) (342055077971371 / 10000000000000000 : ℝ)
    (cell12411 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · norm_num [cell12411]
  · have h := gap_lower (n := 12411) (a := (82731021722097 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (91552137011 / 4000000000000 : ℝ))
      (E := (cell12411 ⟨39, by decide⟩).energy) (xi := (342055077971371 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12411 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12411]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12411])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12411) (a := (82731021722097 / 100000000000000 : ℝ)) (b := (10375873077 / 6250000000000 : ℝ)) (q := (91552137011 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12411])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12411]

theorem cert12412_20 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41691897057059 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288591784449 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨20, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41691897057059 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288591784449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_21 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83349219856461 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572148953631 / 25000000000000 : ℝ))
      (E := (cell12412 ⟨21, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83349219856461 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572148953631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_22 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20828667491393 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572149946517 / 25000000000000 : ℝ))
      (E := (cell12412 ⟨22, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20828667491393 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572149946517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_23 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41640072204157 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1430377351 / 62500000000 : ℝ))
      (E := (cell12412 ⟨23, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41640072204157 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1430377351 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_24 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83245643151717 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288607803503 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨24, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83245643151717 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288607803503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_25 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (16642233232597 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (228861179891 / 10000000000000 : ℝ))
      (E := (cell12412 ⟨25, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (16642233232597 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (228861179891 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_26 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83176713409489 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144307875657 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨26, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83176713409489 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144307875657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_27 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (16628456971753 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1430387363 / 62500000000 : ℝ))
      (E := (cell12412 ⟨27, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (16628456971753 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1430387363 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_28 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83107880478521 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (286077971707 / 12500000000000 : ℝ))
      (E := (cell12412 ⟨28, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83107880478521 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (286077971707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_29 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (664588001893 / 800000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144313895567 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨29, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (664588001893 / 800000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144313895567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_30 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (16607828820223 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (71519743043 / 3125000000000 : ℝ))
      (E := (cell12412 ⟨30, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (16607828820223 / 20000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (71519743043 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_31 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (83004812040187 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288635734711 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨31, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (83004812040187 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288635734711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_32 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20742626005551 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (286079972787 / 12500000000000 : ℝ))
      (E := (cell12412 ⟨32, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20742626005551 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (286079972787 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_33 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (82936220015689 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (91545749859 / 4000000000000 : ℝ))
      (E := (cell12412 ⟨33, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (82936220015689 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (91545749859 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_34 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (20725489997331 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572161936493 / 25000000000000 : ℝ))
      (E := (cell12412 ⟨34, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (20725489997331 / 25000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572161936493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_35 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (82867723911953 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572162930917 / 25000000000000 : ℝ))
      (E := (cell12412 ⟨35, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (82867723911953 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572162930917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_36 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41416755876289 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572163934843 / 25000000000000 : ℝ))
      (E := (cell12412 ⟨36, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41416755876289 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (572163934843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_37 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (41399661740179 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (286082466933 / 12500000000000 : ℝ))
      (E := (cell12412 ⟨37, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (41399661740179 / 50000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (286082466933 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_38 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (2586411220769 / 3125000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288663771353 / 100000000000000 : ℝ))
      (E := (cell12412 ⟨38, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (2586411220769 / 3125000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (2288663771353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12412_39 : CellCertificate 12412 (894915607003999 / 10000000000000000 : ℝ) (211535096554401 / 125000000000000000 : ℝ) (85506702029039 / 2500000000000000 : ℝ)
    (cell12412 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · norm_num [cell12412]
  · have h := gap_lower (n := 12412) (a := (82731018474801 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144333865113 / 50000000000000 : ℝ))
      (E := (cell12412 ⟨39, by decide⟩).energy) (xi := (85506702029039 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12412 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12412]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12412])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12412) (a := (82731018474801 / 100000000000000 : ℝ)) (b := (166000421307 / 100000000000000 : ℝ)) (q := (1144333865113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12412])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12412]

theorem cert12413_20 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83383784818719 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572114032467 / 25000000000000 : ℝ))
      (E := (cell12413 ⟨20, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83383784818719 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572114032467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_21 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83349210883447 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286057515417 / 12500000000000 : ℝ))
      (E := (cell12413 ⟨21, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83349210883447 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (286057515417 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_22 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (20828665328623 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144232058647 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨22, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (20828665328623 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144232058647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_23 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83280136078717 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (457693623203 / 20000000000000 : ℝ))
      (E := (cell12413 ⟨23, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83280136078717 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (457693623203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_24 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (20811408785789 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572118030883 / 25000000000000 : ℝ))
      (E := (cell12413 ⟨24, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (20811408785789 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572118030883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_25 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83211158475011 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572119035911 / 25000000000000 : ℝ))
      (E := (cell12413 ⟨25, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83211158475011 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572119035911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_26 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (16635341208331 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144240060761 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨26, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (16635341208331 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144240060761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_27 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (133027644497 / 160000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144242059419 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨27, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (133027644497 / 160000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144242059419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_28 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (83107873749629 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288488138681 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨28, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (83107873749629 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288488138681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_29 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41536746913269 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572123031363 / 25000000000000 : ℝ))
      (E := (cell12413 ⟨29, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41536746913269 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572123031363 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_30 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (20759784502347 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288496140191 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨30, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (20759784502347 / 25000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288496140191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_31 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41502403133189 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572125031697 / 25000000000000 : ℝ))
      (E := (cell12413 ⟨31, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41502403133189 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572125031697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_32 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82970498565871 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572126036467 / 25000000000000 : ℝ))
      (E := (cell12413 ⟨32, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82970498565871 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572126036467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_33 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (8293621487639 / 10000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144254070407 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨33, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (8293621487639 / 10000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144254070407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_34 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (4145097758331 / 5000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288512113263 / 100000000000000 : ℝ))
      (E := (cell12413 ⟨34, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (4145097758331 / 5000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (2288512113263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_35 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (16573543881081 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144258061613 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨35, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (16573543881081 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144258061613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_36 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (41416753780873 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144260056667 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨36, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (41416753780873 / 50000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144260056667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_37 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (16559863920961 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (35758188821 / 1562500000000 : ℝ))
      (E := (cell12413 ⟨37, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (16559863920961 / 20000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (35758188821 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_38 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82765155503897 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144264048131 / 50000000000000 : ℝ))
      (E := (cell12413 ⟨38, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82765155503897 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (1144264048131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12413_39 : CellCertificate 12413 (894886412983813 / 10000000000000000 : ℝ) (846072197623361 / 500000000000000000 : ℝ) (341998543030547 / 10000000000000000 : ℝ)
    (cell12413 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · norm_num [cell12413]
  · have h := gap_lower (n := 12413) (a := (82731015228497 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572133022593 / 25000000000000 : ℝ))
      (E := (cell12413 ⟨39, by decide⟩).energy) (xi := (341998543030547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12413 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12413]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12413])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12413) (a := (82731015228497 / 100000000000000 : ℝ)) (b := (165986875617 / 100000000000000 : ℝ)) (q := (572133022593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12413])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12413]

theorem cert12414_20 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83383775525061 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288320587517 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨20, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83383775525061 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288320587517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_21 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83349201912133 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288324544467 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨21, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83349201912133 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288324544467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_22 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (5207165791567 / 6250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (71510267529 / 3125000000000 : ℝ))
      (E := (cell12414 ⟨22, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (5207165791567 / 6250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (71510267529 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_23 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41640063875371 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288332582923 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨23, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41640063875371 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288332582923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_24 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (5202851696011 / 6250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288336556143 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨24, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (5202851696011 / 6250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288336556143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_25 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83211150788579 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288340542681 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨25, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83211150788579 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288340542681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_26 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41588349337661 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288344546099 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨26, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41588349337661 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288344546099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_27 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83142270763947 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288348569721 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨27, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83142270763947 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288348569721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_28 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (1038848337777 / 1250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288352558203 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨28, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (1038848337777 / 1250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288352558203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_29 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41536743708917 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288356572791 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨29, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41536743708917 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288356572791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_30 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (20759782979751 / 25000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (35755633713 / 1562500000000 : ℝ))
      (E := (cell12414 ⟨30, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (20759782979751 / 25000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (35755633713 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_31 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (83004800493873 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144182257523 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨31, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (83004800493873 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144182257523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_32 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41485246555401 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144184282097 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨32, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41485246555401 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144184282097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_33 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82936209738317 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (457674506283 / 20000000000000 : ℝ))
      (E := (cell12414 ⟨33, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82936209738317 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (457674506283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_34 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41450975172551 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288376535433 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨34, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41450975172551 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288376535433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_35 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (82867714900003 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144190259563 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨35, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (82867714900003 / 100000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144190259563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_36 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41416751686011 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288384542303 / 100000000000000 : ℝ))
      (E := (cell12414 ⟨36, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41416751686011 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (2288384542303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_37 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (1034991446629 / 1250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (143024284209 / 6250000000000 : ℝ))
      (E := (cell12414 ⟨37, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (1034991446629 / 1250000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (143024284209 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_38 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (10345643993027 / 12500000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144196267489 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨38, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (10345643993027 / 12500000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144196267489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12414_39 : CellCertificate 12414 (894857223489927 / 10000000000000000 : ℝ) (1692008040037139 / 1000000000000000000 : ℝ) (341970282713197 / 10000000000000000 : ℝ)
    (cell12414 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · norm_num [cell12414]
  · have h := gap_lower (n := 12414) (a := (41365505991591 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144198252859 / 50000000000000 : ℝ))
      (E := (cell12414 ⟨39, by decide⟩).energy) (xi := (341970282713197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12414 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12414]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12414])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12414) (a := (41365505991591 / 50000000000000 : ℝ)) (b := (165973332161 / 100000000000000 : ℝ)) (q := (1144198252859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12414])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12414]

theorem cert12415_20 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (10422970779143 / 12500000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288185040901 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨20, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (10422970779143 / 12500000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288185040901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_21 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (2083729823563 / 2500000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144094509823 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨21, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (2083729823563 / 2500000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144094509823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_22 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83314644017313 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144096529337 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨22, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83314644017313 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144096529337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_23 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83280119424387 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288197045689 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨23, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83280119424387 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288197045689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_24 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83245619130777 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572050260749 / 25000000000000 : ℝ))
      (E := (cell12415 ⟨24, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83245619130777 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (572050260749 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_25 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83211143103687 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (286025631799 / 12500000000000 : ℝ))
      (E := (cell12415 ⟨25, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83211143103687 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (286025631799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_26 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83176691310491 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144104512523 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨26, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83176691310491 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144104512523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_27 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83142263718731 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (18305704133 / 800000000000 : ℝ))
      (E := (cell12415 ⟨27, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83142263718731 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (18305704133 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_28 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83107860296113 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144108516111 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨28, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83107860296113 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144108516111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_29 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83073481010511 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144110508117 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨29, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83073481010511 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144110508117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_30 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83039125829963 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288225029699 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨30, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83039125829963 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288225029699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_31 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (83004794722671 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288229016503 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨31, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (83004794722671 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288229016503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_32 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82970487656997 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288233037273 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨32, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82970487656997 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288233037273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_33 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (20734051150367 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288237035389 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨33, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (20734051150367 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288237035389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_34 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82901945524769 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144120506243 / 50000000000000 : ℝ))
      (E := (cell12415 ⟨34, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82901945524769 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (1144120506243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_35 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41433855197873 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (91529801143 / 4000000000000 : ℝ))
      (E := (cell12415 ⟨35, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41433855197873 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (91529801143 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_36 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (20708374795851 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288249026283 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨36, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (20708374795851 / 25000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288249026283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_37 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (82799311856903 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (286031625821 / 12500000000000 : ℝ))
      (E := (cell12415 ⟨37, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (82799311856903 / 100000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (286031625821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_38 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (41382574192781 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288257028833 / 100000000000000 : ℝ))
      (E := (cell12415 ⟨38, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (41382574192781 / 50000000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (2288257028833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12415_39 : CellCertificate 12415 (223707009630309 / 2500000000000000 : ℝ) (338374341360229 / 200000000000000000 : ℝ) (8548550679069 / 250000000000000 : ℝ)
    (cell12415 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · norm_num [cell12415]
  · have h := gap_lower (n := 12415) (a := (10341376092357 / 12500000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457652195253 / 20000000000000 : ℝ))
      (E := (cell12415 ⟨39, by decide⟩).energy) (xi := (8548550679069 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12415 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12415]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12415])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12415) (a := (10341376092357 / 12500000000000 : ℝ)) (b := (82979895469 / 50000000000000 : ℝ)) (q := (457652195253 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12415])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12415]

theorem cert12416_20 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83383756942967 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288049606517 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨20, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83383756942967 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288049606517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_21 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (5209323998413 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (286006700893 / 12500000000000 : ℝ))
      (E := (cell12416 ⟨21, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (5209323998413 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (286006700893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_22 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (41657317685607 / 50000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288057610533 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨22, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (41657317685607 / 50000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288057610533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_23 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83280111099653 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288061562631 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨23, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83280111099653 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288061562631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_24 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (41622805563479 / 50000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (228806558409 / 10000000000000 : ℝ))
      (E := (cell12416 ⟨24, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (41622805563479 / 50000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (228806558409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_25 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (5200695963771 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288069562041 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨25, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (5200695963771 / 6250000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288069562041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_26 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83176683947161 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144036779181 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨26, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83176683947161 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144036779181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_27 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (3325690266999 / 4000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144038788189 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨27, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (3325690266999 / 4000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144038788189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_28 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83107853571487 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288081560741 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨28, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83107853571487 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288081560741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_29 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83073474604571 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144042786349 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨29, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83073474604571 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144042786349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_30 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (16607823948453 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288089556391 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨30, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (16607823948453 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288089556391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_31 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (83004788952771 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (45761871453 / 2000000000000 : ℝ))
      (E := (cell12416 ⟨31, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (83004788952771 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (45761871453 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_32 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (16594096440891 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572024391277 / 25000000000000 : ℝ))
      (E := (cell12416 ⟨32, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (16594096440891 / 20000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (572024391277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_33 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82936199465843 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144050767813 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨33, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82936199465843 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144050767813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_34 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82901940705621 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288105544421 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨34, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82901940705621 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288105544421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_35 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (20716926473159 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288109534367 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨35, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (20716926473159 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288109534367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_36 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (20708373748973 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288113565273 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨36, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (20708373748973 / 25000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288113565273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_37 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82799307984553 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144058760433 / 50000000000000 : ℝ))
      (E := (cell12416 ⟨37, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82799307984553 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (1144058760433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_38 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (82765144827937 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288121519151 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨38, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (82765144827937 / 100000000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288121519151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12416_39 : CellCertificate 12416 (5592492862979 / 62500000000000 : ℝ) (169173539553343 / 100000000000000000 : ℝ) (341913776377891 / 10000000000000000 : ℝ)
    (cell12416 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · norm_num [cell12416]
  · have h := gap_lower (n := 12416) (a := (517068784347 / 625000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288125560707 / 100000000000000 : ℝ))
      (E := (cell12416 ⟨39, by decide⟩).energy) (xi := (341913776377891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12416 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12416]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12416])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12416) (a := (517068784347 / 625000000000 : ℝ)) (b := (165946251949 / 100000000000000 : ℝ)) (q := (2288125560707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12416])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12416]

theorem cert12417_20 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83383747654529 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287914167871 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨20, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83383747654529 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287914167871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_21 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (16669835001679 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143959095211 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨21, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (16669835001679 / 20000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143959095211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_22 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (3332585069071 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287922158211 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨22, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (3332585069071 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287922158211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_23 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41640051388269 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (91517047683 / 4000000000000 : ℝ))
      (E := (cell12417 ⟨23, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41640051388269 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (91517047683 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_24 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83245603124719 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287930179429 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨24, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83245603124719 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287930179429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_25 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (3328445109541 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143967091183 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨25, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (3328445109541 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143967091183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_26 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (83176676585331 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (571984536513 / 25000000000000 : ℝ))
      (E := (cell12417 ⟨26, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (83176676585331 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (571984536513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_27 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (2078556240817 / 2500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (285992773821 / 12500000000000 : ℝ))
      (E := (cell12417 ⟨27, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (2078556240817 / 2500000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (285992773821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_28 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41553923424141 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287946143761 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨28, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41553923424141 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287946143761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_29 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (20768367050003 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287950183729 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨29, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (20768367050003 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287950183729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_30 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (20759778413977 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143977068857 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨30, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (20759778413977 / 25000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143977068857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_31 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (3320191327367 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287958124983 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨31, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (3320191327367 / 4000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287958124983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_32 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82970476753177 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287962147699 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨32, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82970476753177 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287962147699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_33 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (41468097165721 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (57199153731 / 2500000000000 : ℝ))
      (E := (cell12417 ⟨33, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (41468097165721 / 50000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (57199153731 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_34 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82901935887657 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143985065621 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨34, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82901935887657 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143985065621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_35 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82867701390671 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (228797415371 / 10000000000000 : ℝ))
      (E := (cell12417 ⟨35, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82867701390671 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (228797415371 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_36 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82833490809487 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (91519126371 / 4000000000000 : ℝ))
      (E := (cell12417 ⟨36, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82833490809487 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (91519126371 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_37 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (8279930411327 / 10000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287982148889 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨37, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (8279930411327 / 10000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287982148889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_38 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (4138257063567 / 5000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143993061641 / 50000000000000 : ℝ))
      (E := (cell12417 ⟨38, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (4138257063567 / 5000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (1143993061641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12417_39 : CellCertificate 12417 (178953936431007 / 2000000000000000 : ℝ) (422899776557171 / 250000000000000000 : ℝ) (85471382589311 / 2500000000000000 : ℝ)
    (cell12417 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · norm_num [cell12417]
  · have h := gap_lower (n := 12417) (a := (82731002253173 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287990141657 / 100000000000000 : ℝ))
      (E := (cell12417 ⟨39, by decide⟩).energy) (xi := (85471382589311 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12417 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12417]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12417])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12417) (a := (82731002253173 / 100000000000000 : ℝ)) (b := (165932715191 / 100000000000000 : ℝ)) (q := (2287990141657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12417])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12417]

theorem cert12418_20 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83383738367831 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (114388942073 / 5000000000000 : ℝ))
      (E := (cell12418 ⟨20, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83383738367831 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (114388942073 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_21 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83349166043881 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (9151131311 / 400000000000 : ℝ))
      (E := (cell12418 ⟨21, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83349166043881 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (9151131311 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_22 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (16662923616799 / 20000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287786818301 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨22, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (16662923616799 / 20000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287786818301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_23 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41640047227521 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143895408689 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨23, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41640047227521 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143895408689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_24 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83245595124059 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287794829013 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨24, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83245595124059 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287794829013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_25 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83211120058253 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285974849829 / 12500000000000 : ℝ))
      (E := (cell12418 ⟨25, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83211120058253 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285974849829 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_26 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83176669225001 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285975355813 / 12500000000000 : ℝ))
      (E := (cell12418 ⟨26, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83176669225001 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285975355813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_27 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41571121295923 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (114390340039 / 5000000000000 : ℝ))
      (E := (cell12418 ⟨27, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41571121295923 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (114390340039 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_28 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41553920063249 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287810839719 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨28, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41553920063249 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287810839719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_29 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41536730898417 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287814790863 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨29, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41536730898417 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287814790863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_30 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (83039107570893 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (45756376643 / 2000000000000 : ℝ))
      (E := (cell12418 ⟨30, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (83039107570893 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (45756376643 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_31 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (1037559717711 / 1250000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287822790517 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨31, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (1037559717711 / 1250000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287822790517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_32 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (82970471303161 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285978348131 / 12500000000000 : ℝ))
      (E := (cell12418 ⟨32, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (82970471303161 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (285978348131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_33 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (10367023649783 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (91513232707 / 4000000000000 : ℝ))
      (E := (cell12418 ⟨33, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (10367023649783 / 12500000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (91513232707 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_34 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41450965535439 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143917386473 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨34, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41450965535439 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143917386473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_35 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (1657353937797 / 2000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287838769401 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨35, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (1657353937797 / 2000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287838769401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_36 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (20708371656047 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (71495087759 / 3125000000000 : ℝ))
      (E := (cell12418 ⟨36, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (20708371656047 / 25000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (71495087759 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_37 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (41399650121527 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143923386669 / 50000000000000 : ℝ))
      (E := (cell12418 ⟨37, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (41399650121527 / 50000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (1143923386669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_38 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (82765137715771 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287850782551 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨38, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (82765137715771 / 100000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287850782551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12418_39 : CellCertificate 12418 (894740510755321 / 10000000000000000 : ℝ) (1057164274301 / 625000000000000 : ℝ) (341857289099477 / 10000000000000000 : ℝ)
    (cell12418 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · norm_num [cell12418]
  · have h := gap_lower (n := 12418) (a := (16546199802363 / 20000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287854777809 / 100000000000000 : ℝ))
      (E := (cell12418 ⟨39, by decide⟩).energy) (xi := (341857289099477 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12418 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12418]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12418])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12418) (a := (16546199802363 / 20000000000000 : ℝ)) (b := (82959590333 / 50000000000000 : ℝ)) (q := (2287854777809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12418])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12418]

theorem cert12419_20 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (10422966135359 / 12500000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287643569037 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨20, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (10422966135359 / 12500000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287643569037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_21 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41674578540533 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287647519131 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨21, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41674578540533 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287647519131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_22 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41657304721437 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287651532507 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨22, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41657304721437 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287651532507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_23 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41640043067583 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287655555181 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨23, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41640043067583 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287655555181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_24 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83245587124979 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287659532841 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨24, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83245587124979 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287659532841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_25 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83211112379521 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (285957940947 / 12500000000000 : ℝ))
      (E := (cell12419 ⟨25, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83211112379521 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (285957940947 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_26 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (8317666186617 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143833771471 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨26, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (8317666186617 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143833771471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_27 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83142235552471 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457534304769 / 20000000000000 : ℝ))
      (E := (cell12419 ⟨27, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83142235552471 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457534304769 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_28 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41553916703067 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287675531743 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨28, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41553916703067 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287675531743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_29 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83073455395037 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143839755513 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨29, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83073455395037 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143839755513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_30 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83039101487219 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287683522733 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨30, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83039101487219 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287683522733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_31 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (83004771650887 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143843755373 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨31, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (83004771650887 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143843755373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_32 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (10371308231801 / 12500000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287691535687 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨32, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (10371308231801 / 12500000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287691535687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_33 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (8293618406631 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571923885233 / 25000000000000 : ℝ))
      (E := (cell12419 ⟨33, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (8293618406631 / 10000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571923885233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_34 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82901926255283 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457539905623 / 20000000000000 : ℝ))
      (E := (cell12419 ⟨34, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82901926255283 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (457539905623 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_35 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (3314707695607 / 4000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143851749321 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨35, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (3314707695607 / 4000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143851749321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_36 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (41416741219997 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571926878079 / 25000000000000 : ℝ))
      (E := (cell12419 ⟨36, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (41416741219997 / 50000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (571926878079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_37 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (16559859274781 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287711511513 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨37, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (16559859274781 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287711511513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_38 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (82765134161229 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143857748481 / 50000000000000 : ℝ))
      (E := (cell12419 ⟨38, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (82765134161229 / 100000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (1143857748481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12419_39 : CellCertificate 12419 (223677835969099 / 2500000000000000 : ℝ) (1691326593486871 / 1000000000000000000 : ℝ) (68365810520649 / 2000000000000000 : ℝ)
    (cell12419 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · norm_num [cell12419]
  · have h := gap_lower (n := 12419) (a := (16546199154289 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287719527863 / 100000000000000 : ℝ))
      (E := (cell12419 ⟨39, by decide⟩).energy) (xi := (68365810520649 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12419 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12419]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12419])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12419) (a := (16546199154289 / 20000000000000 : ℝ)) (b := (41476412093 / 25000000000000 : ℝ)) (q := (2287719527863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12419])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12419]

theorem cert12420_20 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83383719799651 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143754146177 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨20, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83383719799651 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143754146177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_21 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83349148119949 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (57187808071 / 2500000000000 : ℝ))
      (E := (cell12420 ⟨21, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83349148119949 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (57187808071 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_22 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (20828650200853 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (71484884401 / 3125000000000 : ℝ))
      (E := (cell12420 ⟨22, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (20828650200853 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (71484884401 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_23 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (20820019454227 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (142970018053 / 6250000000000 : ℝ))
      (E := (cell12420 ⟨23, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (20820019454227 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (142970018053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_24 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83245579127477 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287524290917 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨24, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83245579127477 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287524290917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_25 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (10401388087791 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287528310831 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨25, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (10401388087791 / 12500000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287528310831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_26 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (83176654508839 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143766146877 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨26, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (83176654508839 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143766146877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_27 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (20785557128639 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287536301351 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨27, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (20785557128639 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287536301351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_28 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (8310782668719 / 10000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (228754027827 / 10000000000000 : ℝ))
      (E := (cell12420 ⟨28, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (8310782668719 / 10000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (228754027827 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_29 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (4153672449731 / 5000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287544285757 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨29, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (4153672449731 / 5000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287544285757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_30 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41519547702443 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571887066987 / 25000000000000 : ℝ))
      (E := (cell12420 ⟨30, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41519547702443 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571887066987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_31 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (20751191471549 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287552285671 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨31, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (20751191471549 / 25000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287552285671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_32 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82970460406917 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143778141277 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨32, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82970460406917 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143778141277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_33 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (41468089467789 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287560260459 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨33, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (41468089467789 / 50000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287560260459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_34 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82901921440871 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143782139797 / 50000000000000 : ℝ))
      (E := (cell12420 ⟨34, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82901921440871 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (1143782139797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_35 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82867687891643 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571892070709 / 25000000000000 : ℝ))
      (E := (cell12420 ⟨35, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82867687891643 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (571892070709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_36 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (16566695651381 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287572271359 / 100000000000000 : ℝ))
      (E := (cell12420 ⟨36, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (16566695651381 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (2287572271359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_37 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (82799292505821 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (17871689881 / 781250000000 : ℝ))
      (E := (cell12420 ⟨37, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (82799292505821 / 100000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (17871689881 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_38 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (16553026121543 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (457516053303 / 20000000000000 : ℝ))
      (E := (cell12420 ⟨38, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (16553026121543 / 20000000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (457516053303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12420_39 : CellCertificate 12420 (894682181517159 / 10000000000000000 : ℝ) (1691190370039193 / 1000000000000000000 : ℝ) (170900410433603 / 5000000000000000 : ℝ)
    (cell12420 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · norm_num [cell12420]
  · have h := gap_lower (n := 12420) (a := (2585343516627 / 3125000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (91503370977 / 4000000000000 : ℝ))
      (E := (cell12420 ⟨39, by decide⟩).energy) (xi := (170900410433603 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12420 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12420]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12420])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12420) (a := (2585343516627 / 3125000000000 : ℝ)) (b := (165892118309 / 100000000000000 : ℝ)) (q := (91503370977 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12420])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12420]

theorem cert12421_20 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (10422963814771 / 12500000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (285921640989 / 12500000000000 : ℝ))
      (E := (cell12421 ⟨20, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (10422963814771 / 12500000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (285921640989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_21 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (8334913916053 / 10000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (228737712233 / 10000000000000 : ℝ))
      (E := (cell12421 ⟨21, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (8334913916053 / 10000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (228737712233 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_22 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83314592165607 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287381123277 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨22, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83314592165607 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287381123277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_23 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (20820017375067 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (114369256751 / 5000000000000 : ℝ))
      (E := (cell12421 ⟨23, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (20820017375067 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (114369256751 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_24 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83245571131553 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287389161587 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨24, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83245571131553 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287389161587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_25 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83211097026673 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (5718482871 / 250000000000 : ℝ))
      (E := (cell12421 ⟨25, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83211097026673 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (5718482871 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_26 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83176647153007 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143698578667 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨26, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83176647153007 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143698578667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_27 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (831422214781 / 1000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287401133297 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨27, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (831422214781 / 1000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287401133297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_28 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41553909984833 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287405137741 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨28, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41553909984833 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287405137741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_29 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (83073442595583 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287409115057 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨29, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (83073442595583 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287409115057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_30 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41519544661947 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287413126281 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨30, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41519544661947 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287413126281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_31 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41502380061403 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287417115293 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨31, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41502380061403 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287417115293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_32 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (5185653435043 / 6250000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143710571357 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨32, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (5185653435043 / 6250000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143710571357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_33 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82936173806069 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457485018673 / 20000000000000 : ℝ))
      (E := (cell12421 ⟨33, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82936173806069 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457485018673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_34 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (41450958313821 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287429085963 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨34, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (41450958313821 / 50000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287429085963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_35 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (5179230212141 / 6250000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143716560991 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨35, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (5179230212141 / 6250000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143716560991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_36 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82833474074921 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287437085419 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨36, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82833474074921 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287437085419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_37 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (20699822159701 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143720547227 / 50000000000000 : ℝ))
      (E := (cell12421 ⟨37, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (20699822159701 / 25000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (1143720547227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_38 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (82765127055227 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287445091211 / 100000000000000 : ℝ))
      (E := (cell12421 ⟨38, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (82765127055227 / 100000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (2287445091211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12421_39 : CellCertificate 12421 (89465302367651 / 1000000000000000 : ℝ) (1691054168533263 / 1000000000000000000 : ℝ) (341772593890017 / 10000000000000000 : ℝ)
    (cell12421 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · norm_num [cell12421]
  · have h := gap_lower (n := 12421) (a := (8273098929367 / 10000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457489815239 / 20000000000000 : ℝ))
      (E := (cell12421 ⟨39, by decide⟩).energy) (xi := (341772593890017 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12421 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12421]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12421])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12421) (a := (8273098929367 / 10000000000000 : ℝ)) (b := (41469647619 / 25000000000000 : ℝ)) (q := (457489815239 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12421])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12421]

theorem cert12422_20 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41691850619211 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287238017463 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨20, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41691850619211 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287238017463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_21 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83349130202809 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287242034151 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨21, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83349130202809 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287242034151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_22 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (4165729176473 / 5000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571811499961 / 25000000000000 : ℝ))
      (E := (cell12422 ⟨22, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (4165729176473 / 5000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571811499961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_23 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (16656012237049 / 20000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287250035379 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨23, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (16656012237049 / 20000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287250035379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_24 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83245563137207 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287254028163 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨24, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83245563137207 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287254028163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_25 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (20802772338139 / 25000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287258040283 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨25, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (20802772338139 / 25000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287258040283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_26 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (5198539987417 / 6250000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (285907752113 / 12500000000000 : ℝ))
      (E := (cell12422 ⟨26, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (5198539987417 / 6250000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (285907752113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_27 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41571107221551 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (285908252461 / 12500000000000 : ℝ))
      (E := (cell12422 ⟨27, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41571107221551 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (285908252461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_28 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (2077695331339 / 2500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287269993283 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨28, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (2077695331339 / 2500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287269993283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_29 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41536718098963 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287273998929 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨29, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41536718098963 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287273998929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_30 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41519541622121 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457455596153 / 20000000000000 : ℝ))
      (E := (cell12422 ⟨30, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41519541622121 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457455596153 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_31 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (83004754360717 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457456399923 / 20000000000000 : ℝ))
      (E := (cell12422 ⟨31, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (83004754360717 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (457456399923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_32 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (82970449515719 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571821499777 / 25000000000000 : ℝ))
      (E := (cell12422 ⟨32, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (82970449515719 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (571821499777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_33 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41468084338891 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287289981099 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨33, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41468084338891 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287289981099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_34 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (20725477953899 / 25000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (11436470029 / 500000000000 : ℝ))
      (E := (cell12422 ⟨34, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (20725477953899 / 25000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (11436470029 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_35 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (82867678898013 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143649008041 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨35, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (82867678898013 / 100000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143649008041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_36 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41416734947021 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143651006561 / 50000000000000 : ℝ))
      (E := (cell12422 ⟨36, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41416734947021 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (1143651006561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_37 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (20699821193213 / 25000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228730599787 / 10000000000000 : ℝ))
      (E := (cell12422 ⟨37, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (20699821193213 / 25000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228730599787 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_38 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (41382561751883 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287309971053 / 100000000000000 : ℝ))
      (E := (cell12422 ⟨38, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (41382561751883 / 50000000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (2287309971053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12422_39 : CellCertificate 12422 (894623870353349 / 10000000000000000 : ℝ) (1690917988963781 / 1000000000000000000 : ℝ) (170872185835169 / 5000000000000000 : ℝ)
    (cell12422 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · norm_num [cell12422]
  · have h := gap_lower (n := 12422) (a := (10341373257033 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228731399187 / 10000000000000 : ℝ))
      (E := (cell12422 ⟨39, by decide⟩).energy) (xi := (170872185835169 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12422 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12422]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12422])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12422) (a := (10341373257033 / 12500000000000 : ℝ)) (b := (20733133109 / 12500000000000 : ℝ)) (q := (228731399187 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12422])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12422]

theorem cert12423_20 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (41691845980207 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287102961007 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨20, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (41691845980207 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287102961007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_21 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (1302330019481 / 1562500000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287107000031 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨21, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (1302330019481 / 1562500000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287107000031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_22 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (8331457489497 / 10000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287110988831 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨22, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (8331457489497 / 10000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287110988831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_23 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (520500330449 / 625000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571778747481 / 25000000000000 : ℝ))
      (E := (cell12423 ⟨23, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (520500330449 / 625000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571778747481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_24 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (83245555144439 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287118948989 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨24, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (83245555144439 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287118948989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_25 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (83211081679977 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143561493241 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨25, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (83211081679977 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143561493241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_26 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (20794158111459 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287126930853 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨26, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (20794158111459 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287126930853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_27 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (83142207409563 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287130960523 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨27, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (83142207409563 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287130960523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_28 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (41553903269437 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287134961769 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨28, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (41553903269437 / 50000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287134961769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_29 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (5192089362603 / 6250000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143569468687 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨29, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (5192089362603 / 6250000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143569468687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_30 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (83039077165929 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287142948371 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨30, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (83039077165929 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287142948371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_31 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (83004748599927 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143573469319 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨31, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (83004748599927 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143573469319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_32 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (20742611018003 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571787742199 / 25000000000000 : ℝ))
      (E := (cell12423 ⟨32, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (20742611018003 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (571787742199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_33 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82936163550717 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (114357746183 / 5000000000000 : ℝ))
      (E := (cell12423 ⟨33, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82936163550717 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (114357746183 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_34 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (20725476751183 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (71473716311 / 3125000000000 : ℝ))
      (E := (cell12423 ⟨34, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (20725476751183 / 25000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (71473716311 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_35 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (2589614825091 / 3125000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287162965139 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨35, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (2589614825091 / 3125000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287162965139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_36 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (82833465714267 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287166937219 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨36, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (82833465714267 / 100000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287166937219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_37 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (16559856181593 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287170956369 / 100000000000000 : ℝ))
      (E := (cell12423 ⟨37, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (16559856181593 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (2287170956369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_38 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (8276511995333 / 10000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143587453021 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨38, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (8276511995333 / 10000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143587453021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12423_39 : CellCertificate 12423 (55912170096661 / 625000000000000 : ℝ) (211347728915681 / 125000000000000000 : ℝ) (85429038551707 / 2500000000000000 : ℝ)
    (cell12423 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · norm_num [cell12423]
  · have h := gap_lower (n := 12423) (a := (16546196563969 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143589452029 / 50000000000000 : ℝ))
      (E := (cell12423 ⟨39, by decide⟩).energy) (xi := (85429038551707 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12423 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12423]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12423])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12423) (a := (16546196563969 / 20000000000000 : ℝ)) (b := (165851541497 / 100000000000000 : ℝ)) (q := (1143589452029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12423])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12423]

theorem cert12424_20 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41691841342071 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457393591709 / 20000000000000 : ℝ))
      (E := (cell12424 ⟨20, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41691841342071 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457393591709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_21 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83349112292457 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457394392339 / 20000000000000 : ℝ))
      (E := (cell12424 ⟨21, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83349112292457 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457394392339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_22 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (10414320782767 / 12500000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457395194729 / 20000000000000 : ℝ))
      (E := (cell12424 ⟨22, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (10414320782767 / 12500000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457395194729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_23 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (20820011140013 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (142936246271 / 6250000000000 : ℝ))
      (E := (cell12424 ⟨23, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (20820011140013 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (142936246271 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_24 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83245547153247 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286983982413 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨24, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83245547153247 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286983982413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_25 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (10401384251117 / 12500000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286987986997 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨25, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (10401384251117 / 12500000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2286987986997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_26 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (83176625094497 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143495978787 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨26, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (83176625094497 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143495978787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_27 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41571100188741 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143497977901 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨27, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41571100188741 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143497977901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_28 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (16621559965121 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (285874990791 / 12500000000000 : ℝ))
      (E := (cell12424 ⟨28, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (16621559965121 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (285874990791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_29 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (20768355851687 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (285875491299 / 12500000000000 : ℝ))
      (E := (cell12424 ⟨29, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (20768355851687 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (285875491299 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_30 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (20759767772239 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287007970613 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨30, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (20759767772239 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287007970613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_31 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41502371420219 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287011932361 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨31, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41502371420219 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287011932361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_32 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (41485219314783 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287015934717 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨32, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (41485219314783 / 50000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287015934717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_33 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82936158424873 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287019921051 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨33, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82936158424873 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287019921051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_34 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82901902195051 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287023951573 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨34, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82901902195051 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287023951573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_35 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (16573533981791 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287027910549 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨35, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (16573533981791 / 20000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287027910549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_36 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (20708365383899 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457406383267 / 20000000000000 : ℝ))
      (E := (cell12424 ⟨36, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (20708365383899 / 25000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (457406383267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_37 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82799277044143 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143517955651 / 50000000000000 : ℝ))
      (E := (cell12424 ⟨37, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82799277044143 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (1143517955651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_38 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82765116403921 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287039954849 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨38, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82765116403921 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287039954849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

theorem cert12424_39 : CellCertificate 12424 (223641394313773 / 2500000000000000 : ℝ) (845322847806483 / 500000000000000000 : ℝ) (341687941498147 / 10000000000000000 : ℝ)
    (cell12424 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · norm_num [cell12424]
  · have h := gap_lower (n := 12424) (a := (82730979584413 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287043930153 / 100000000000000 : ℝ))
      (E := (cell12424 ⟨39, by decide⟩).energy) (xi := (341687941498147 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12424 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12424]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12424])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12424) (a := (82730979584413 / 100000000000000 : ℝ)) (b := (165838020351 / 100000000000000 : ℝ)) (q := (2287043930153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12424])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12424]

end BstLean.Part268
