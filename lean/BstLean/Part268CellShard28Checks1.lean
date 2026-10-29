import BstLean.Part268CellShard28Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13050_20 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (20844432138791 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210399577341 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨20, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (20844432138791 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210399577341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_21 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83343329000461 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210403598813 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨21, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83343329000461 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210403598813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_22 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (4165447678457 / 5000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210407621743 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨22, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (4165447678457 / 5000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210407621743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_23 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83274602228551 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (276301448883 / 12500000000000 : ℝ))
      (E := (cell13050 ⟨23, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83274602228551 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (276301448883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_24 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (20810068736553 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552603906649 / 25000000000000 : ℝ))
      (E := (cell13050 ⟨24, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (20810068736553 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552603906649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_25 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (5200373230613 / 6250000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552604903599 / 25000000000000 : ℝ))
      (E := (cell13050 ⟨25, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (5200373230613 / 6250000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552604903599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_26 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (20792923106797 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105211807729 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨26, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (20792923106797 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105211807729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_27 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83137437126367 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210427632161 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨27, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83137437126367 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210427632161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_28 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83103205755521 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210431666657 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨28, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83103205755521 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210431666657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_29 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83068998282991 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210435662341 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨29, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83068998282991 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210435662341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_30 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83034814677277 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210439679379 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨30, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83034814677277 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210439679379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_31 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41500327453521 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210443719233 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨31, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41500327453521 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210443719233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_32 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41483259470553 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210447724543 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨32, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41483259470553 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210447724543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_33 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82932406748449 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210451696249 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨33, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82932406748449 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210451696249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_34 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82898318298207 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210455752343 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨34, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82898318298207 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210455752343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_35 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41432126779837 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105229858731 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨35, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41432126779837 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105229858731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_36 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82830212502299 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210463767861 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨36, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82830212502299 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210463767861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_37 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (16559239019137 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210467786303 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨37, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (16559239019137 / 20000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210467786303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_38 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (82762201309589 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105235886303 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨38, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (82762201309589 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105235886303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_39 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41364115556961 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210475785127 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨39, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41364115556961 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210475785127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13051_20 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (20844428588693 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (110514323369 / 5000000000000 : ℝ))
      (E := (cell13051 ⟨20, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (20844428588693 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (110514323369 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_21 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83343314806317 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105145242471 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨21, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83343314806317 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105145242471 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_22 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83308939381239 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210294504009 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨22, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83308939381239 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210294504009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_23 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (10409323505861 / 12500000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442059705579 / 20000000000000 : ℝ))
      (E := (cell13051 ⟨23, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (10409323505861 / 12500000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442059705579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_24 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41620130385391 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105151250637 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨24, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41620130385391 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105151250637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_25 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (16641191504121 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210306543779 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨25, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (16641191504121 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210306543779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_26 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (5198229891513 / 6250000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442062108237 / 20000000000000 : ℝ))
      (E := (cell13051 ⟨26, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (5198229891513 / 6250000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442062108237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_27 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83137422969603 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105157277141 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨27, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83137422969603 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105157277141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_28 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83103191604969 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210318526717 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨28, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83103191604969 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210318526717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_29 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (16613796827729 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442064515477 / 20000000000000 : ℝ))
      (E := (cell13051 ⟨29, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (16613796827729 / 20000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442064515477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_30 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (20758700134783 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105163295477 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨30, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (20758700134783 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105163295477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_31 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83000640775093 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442066113763 / 20000000000000 : ℝ))
      (E := (cell13051 ⟨31, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83000640775093 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442066113763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_32 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (20741626203837 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105167285363 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨32, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (20741626203837 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105167285363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_33 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (20733098157219 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442067719539 / 20000000000000 : ℝ))
      (E := (cell13051 ⟨33, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (20733098157219 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442067719539 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_34 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41449152092407 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105171295933 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨34, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41449152092407 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105171295933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_35 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (10358029931557 / 12500000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552586653097 / 25000000000000 : ℝ))
      (E := (cell13051 ⟨35, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (10358029931557 / 12500000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552586653097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_36 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (82830198401251 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552587664899 / 25000000000000 : ℝ))
      (E := (cell13051 ⟨36, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (82830198401251 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552587664899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_37 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41398090500401 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552588668723 / 25000000000000 : ℝ))
      (E := (cell13051 ⟨37, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41398090500401 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (552588668723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_38 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41381093610433 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210358658097 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨38, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41381093610433 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210358658097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_39 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41364108515677 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442072533513 / 20000000000000 : ℝ))
      (E := (cell13051 ⟨39, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41364108515677 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (442072533513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13052_20 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41688850078279 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210173411423 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨20, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41688850078279 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210173411423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_21 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83343300614351 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210177425099 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨21, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83343300614351 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210177425099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_22 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (16661785039103 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (138136336373 / 6250000000000 : ℝ))
      (E := (cell13052 ⟨22, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (16661785039103 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (138136336373 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_23 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83274573867401 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105092701019 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨23, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83274573867401 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105092701019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_24 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83240246597527 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552547357513 / 25000000000000 : ℝ))
      (E := (cell13052 ⟨24, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83240246597527 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552547357513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_25 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83205943353577 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210193410427 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨25, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83205943353577 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210193410427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_26 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (415858320517 / 500000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210197462611 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨26, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (415858320517 / 500000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210197462611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_27 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83137408815011 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (22102014721 / 1000000000000 : ℝ))
      (E := (cell13052 ⟨27, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83137408815011 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (22102014721 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_28 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83103177456587 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105102720487 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨28, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83103177456587 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105102720487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_29 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83068969996469 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210209488127 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨29, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83068969996469 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210209488127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_30 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (20758696600789 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210213498229 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨30, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (20758696600789 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210213498229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_31 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (1296884791333 / 1562500000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105108765619 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨31, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (1296884791333 / 1562500000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105108765619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_32 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (20741622672939 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105110764899 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨32, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (20741622672939 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105110764899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_33 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82932378511469 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210225553461 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨33, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82932378511469 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210225553461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_34 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82898290073587 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210229544371 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨34, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82898290073587 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210229544371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_35 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82864225347403 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210233561681 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨35, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82864225347403 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210233561681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_36 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82830184302367 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442047509407 / 20000000000000 : ℝ))
      (E := (cell13052 ⟨36, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82830184302367 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442047509407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_37 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (82796166908081 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210241559189 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨37, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (82796166908081 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210241559189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_38 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (2586317910447 / 3125000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210245598029 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨38, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (2586317910447 / 3125000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210245598029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_39 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41364101475473 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210249604469 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨39, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41364101475473 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210249604469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13053_20 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41688842980261 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105030175579 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨20, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41688842980261 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105030175579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_21 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41671643212281 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210064360949 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨21, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41671643212281 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210064360949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_22 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (650850867281 / 781250000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105034186169 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨22, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (650850867281 / 781250000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105034186169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_23 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (8327455969009 / 10000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210072330257 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨23, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (8327455969009 / 10000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210072330257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_24 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83240232426447 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (88403054181 / 4000000000000 : ℝ))
      (E := (cell13053 ⟨24, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83240232426447 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (88403054181 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_25 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41602964594361 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210080389631 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨25, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41602964594361 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210080389631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_26 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (16634329988953 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210084379733 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨26, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (16634329988953 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210084379733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_27 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83137394662591 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442017677123 / 20000000000000 : ℝ))
      (E := (cell13053 ⟨27, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83137394662591 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442017677123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_28 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83103163310377 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210092409429 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨28, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83103163310377 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210092409429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_29 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83068955856463 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (221009639457 / 10000000000000 : ℝ))
      (E := (cell13053 ⟨29, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83068955856463 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (221009639457 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_30 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83034772269349 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442020080241 / 20000000000000 : ℝ))
      (E := (cell13053 ⟨30, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83034772269349 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442020080241 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_31 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83000612517699 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210104430793 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨31, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83000612517699 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210104430793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_32 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (20741619142583 / 25000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105054212989 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨32, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (20741619142583 / 25000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105054212989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_33 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (20733091099057 / 25000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210112446313 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨33, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (20733091099057 / 25000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210112446313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_34 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (20724568991131 / 25000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105058246291 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨34, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (20724568991131 / 25000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105058246291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_35 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82864211244513 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210120506679 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨35, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82864211244513 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210120506679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_36 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (16566034041129 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (552531122217 / 25000000000000 : ℝ))
      (E := (cell13053 ⟨36, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (16566034041129 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (552531122217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_37 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (82796152817523 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210128497901 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨37, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (82796152817523 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210128497901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_38 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (5172634940619 / 6250000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (552533133417 / 25000000000000 : ℝ))
      (E := (cell13053 ⟨38, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (5172634940619 / 6250000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (552533133417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_39 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41364094436349 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210136537081 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨39, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41364094436349 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210136537081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13054_20 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (16675534353333 / 20000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276243410823 / 12500000000000 : ℝ))
      (E := (cell13054 ⟨20, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (16675534353333 / 20000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276243410823 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_21 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (1666865444739 / 2000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209951292491 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨21, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (1666865444739 / 2000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209951292491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_22 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (20827224207649 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209955300043 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨22, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (20827224207649 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209955300043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_23 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41637272757477 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209959312553 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨23, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41637272757477 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209959312553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_24 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (4162010912877 / 5000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209963333101 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨24, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (4162010912877 / 5000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209963333101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_25 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83205915026039 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552491841133 / 25000000000000 : ℝ))
      (E := (cell13054 ⟨25, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83205915026039 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552491841133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_26 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41585817894151 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (441994270201 / 20000000000000 : ℝ))
      (E := (cell13054 ⟨26, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41585817894151 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (441994270201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_27 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41568690256171 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1104987676653 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨27, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41568690256171 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1104987676653 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_28 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (324621676431 / 390625000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (138123710849 / 6250000000000 : ℝ))
      (E := (cell13054 ⟨28, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (324621676431 / 390625000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (138123710849 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_29 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (664551533749 / 800000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552495838809 / 25000000000000 : ℝ))
      (E := (cell13054 ⟨29, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (664551533749 / 800000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552495838809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_30 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (8303475813771 / 10000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1104993708487 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨30, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (8303475813771 / 10000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1104993708487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_31 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83000598392253 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209991384619 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨31, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83000598392253 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209991384619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_32 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82966462451073 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276249429381 / 12500000000000 : ℝ))
      (E := (cell13054 ⟨32, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82966462451073 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276249429381 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_33 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (5183271892697 / 6250000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209999452103 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨33, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (5183271892697 / 6250000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209999452103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_34 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (663186094861 / 800000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105001718249 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨34, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (663186094861 / 800000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105001718249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_35 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82864197143787 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210007447383 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨35, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82864197143787 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210007447383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_36 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41415078055543 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105005742547 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨36, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41415078055543 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1105005742547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_37 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41398069364563 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276251936379 / 12500000000000 : ℝ))
      (E := (cell13054 ⟨37, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41398069364563 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276251936379 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_38 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82762144967663 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210019465017 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨38, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82762144967663 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2210019465017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_39 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (82728174796609 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (6906323513 / 312500000000 : ℝ))
      (E := (cell13054 ⟨39, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (82728174796609 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (6906323513 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13055_20 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (10422207196873 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209834276017 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨20, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (10422207196873 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209834276017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_21 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41671629025757 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (441967655613 / 20000000000000 : ℝ))
      (E := (cell13055 ⟨21, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41671629025757 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (441967655613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_22 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (416544413257 / 500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209842281803 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨22, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (416544413257 / 500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209842281803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_23 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83274531341991 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209846290547 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨23, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83274531341991 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209846290547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_24 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83240204090807 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209850307373 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨24, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83240204090807 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209850307373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_25 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (8320590086553 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (220985433513 / 10000000000000 : ℝ))
      (E := (cell13055 ⟨25, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (8320590086553 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (220985433513 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_26 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (8317162163401 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209858317977 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨26, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (8317162163401 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209858317977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_27 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83137366364263 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (276232789587 / 12500000000000 : ℝ))
      (E := (cell13055 ⟨27, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83137366364263 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (276232789587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_28 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (16620627004893 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1726458073 / 78125000000 : ℝ))
      (E := (cell13055 ⟨28, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (16620627004893 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1726458073 / 78125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_29 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83068927582957 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104935185063 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨29, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83068927582957 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104935185063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_30 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83034744008239 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209874369899 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨30, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83034744008239 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209874369899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_31 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83000584268973 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (27623479909 / 1250000000000 : ℝ))
      (E := (cell13055 ⟨31, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83000584268973 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (27623479909 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_32 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82966448333981 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209882381229 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨32, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82966448333981 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209882381229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_33 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82932336172241 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209886394981 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨33, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82932336172241 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209886394981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_34 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82898247752891 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209890434759 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨34, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82898247752891 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209890434759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_35 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (10358022880653 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104947221229 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨35, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (10358022880653 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104947221229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_36 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82830142018689 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209898418341 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨36, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82830142018689 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209898418341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_37 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (8279612464289 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209902479871 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨37, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (8279612464289 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209902479871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_38 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (82762130887583 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (276238306351 / 12500000000000 : ℝ))
      (E := (cell13055 ⟨38, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (82762130887583 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (276238306351 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_39 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (2068204018067 / 2500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209910506949 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨39, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (2068204018067 / 2500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209910506949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13056_20 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (2084441084637 / 2500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104860630573 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨20, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (2084441084637 / 2500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104860630573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_21 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41671621934127 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441945051867 / 20000000000000 : ℝ))
      (E := (cell13056 ⟨21, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41671621934127 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441945051867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_22 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83308868474379 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209729317619 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨22, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83308868474379 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209729317619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_23 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83274517171203 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (110486666131 / 5000000000000 : ℝ))
      (E := (cell13056 ⟨23, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83274517171203 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (110486666131 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_24 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41620094963123 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276217166969 / 12500000000000 : ℝ))
      (E := (cell13056 ⟨24, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41620094963123 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276217166969 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_25 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (10400735838399 / 12500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209741301429 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨25, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (10400735838399 / 12500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209741301429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_26 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (8317160748189 / 10000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209745339101 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨26, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (8317160748189 / 10000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209745339101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_27 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (16627470443671 / 20000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276218666783 / 12500000000000 : ℝ))
      (E := (cell13056 ⟨27, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (16627470443671 / 20000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276218666783 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_28 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83103120884763 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209753347499 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨28, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83103120884763 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209753347499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_29 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (5191807090591 / 6250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209757380721 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨29, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (5191807090591 / 6250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209757380721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_30 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (16606945976187 / 20000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552440344269 / 25000000000000 : ℝ))
      (E := (cell13056 ⟨30, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (16606945976187 / 20000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552440344269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_31 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (4150028507393 / 5000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (88390615861 / 4000000000000 : ℝ))
      (E := (cell13056 ⟨31, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (4150028507393 / 5000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (88390615861 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_32 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82966434219053 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (220976938171 / 10000000000000 : ℝ))
      (E := (cell13056 ⟨32, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82966434219053 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (220976938171 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_33 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41466161031747 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209773392183 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨33, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41466161031747 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209773392183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_34 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (1036227920629 / 1250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209777428729 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨34, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (1036227920629 / 1250000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209777428729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_35 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82864168948823 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104890716621 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨35, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82864168948823 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104890716621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_36 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82830127928453 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (69055795771 / 3125000000000 : ℝ))
      (E := (cell13056 ⟨36, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82830127928453 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (69055795771 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_37 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41398055279407 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104894732211 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨37, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41398055279407 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104894732211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_38 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (82762116809663 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552448372761 / 25000000000000 : ℝ))
      (E := (cell13056 ⟨38, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (82762116809663 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552448372761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_39 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (8272814665091 / 10000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (44195949709 / 2000000000000 : ℝ))
      (E := (cell13056 ⟨39, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (8272814665091 / 10000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (44195949709 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13057_20 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (10422203649769 / 12500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209608300283 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨20, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (10422203649769 / 12500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209608300283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_21 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83343229687169 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552403073659 / 25000000000000 : ℝ))
      (E := (cell13057 ⟨21, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83343229687169 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552403073659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_22 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83308854299531 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209616349133 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨22, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83308854299531 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209616349133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_23 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (20818625750647 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (276202543799 / 12500000000000 : ℝ))
      (E := (cell13057 ⟨23, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (20818625750647 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (276202543799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_24 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (41620087881929 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552406089957 / 25000000000000 : ℝ))
      (E := (cell13057 ⟨24, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (41620087881929 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552406089957 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_25 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (3328234902041 / 4000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209628380287 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨25, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (3328234902041 / 4000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209628380287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_26 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (4158579666597 / 5000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209632355927 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨26, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (4158579666597 / 5000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209632355927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_27 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (16627467614923 / 20000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (441927269507 / 20000000000000 : ℝ))
      (E := (cell13057 ⟨27, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (16627467614923 / 20000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (441927269507 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_28 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (8310310674723 / 10000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209640357259 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨28, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (8310310674723 / 10000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209640357259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_29 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (20767224829531 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104822193509 / 50000000000000 : ℝ))
      (E := (cell13057 ⟨29, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (20767224829531 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104822193509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_30 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83034715755797 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209648379957 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨30, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83034715755797 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209648379957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_31 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83000556028913 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (441930479207 / 20000000000000 : ℝ))
      (E := (cell13057 ⟨31, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83000556028913 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (441930479207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_32 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82966420106291 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209656436489 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨32, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82966420106291 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209656436489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_33 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (5183269247307 / 6250000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552415110927 / 25000000000000 : ℝ))
      (E := (cell13057 ⟨33, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (5183269247307 / 6250000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552415110927 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_34 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82898219549911 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209664477047 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨34, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82898219549911 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209664477047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_35 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (10358019356823 / 12500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209668478397 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨35, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (10358019356823 / 12500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209668478397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_36 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82830113840379 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (88386897921 / 4000000000000 : ℝ))
      (E := (cell13057 ⟨36, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82830113840379 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (88386897921 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_37 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82796096476899 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (69052390731 / 3125000000000 : ℝ))
      (E := (cell13057 ⟨37, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82796096476899 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (69052390731 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_38 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (41381051366951 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (138105032937 / 6250000000000 : ℝ))
      (E := (cell13057 ⟨38, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (41381051366951 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (138105032937 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_39 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (82728132581297 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104842259211 / 50000000000000 : ℝ))
      (E := (cell13057 ⟨39, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (82728132581297 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104842259211 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13058_20 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83377615013 / 100000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209495335117 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨20, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83377615013 / 100000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209495335117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_21 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83343215508259 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209499383973 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨21, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83343215508259 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209499383973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_22 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41654420063429 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104751688173 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨22, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41654420063429 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104751688173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_23 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41637244418073 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276188421733 / 12500000000000 : ℝ))
      (E := (cell13058 ⟨23, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41637244418073 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276188421733 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_24 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41620080801821 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104755689803 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨24, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41620080801821 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104755689803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_25 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (8320585839703 / 10000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209515396417 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨25, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (8320585839703 / 10000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209515396417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_26 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (519822369901 / 625000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552379856727 / 25000000000000 : ℝ))
      (E := (cell13058 ⟨26, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (519822369901 / 625000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552379856727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_27 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (16627464786609 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (441904682997 / 20000000000000 : ℝ))
      (E := (cell13058 ⟨27, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (16627464786609 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (441904682997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_28 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (16620618522373 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209527421223 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨28, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (16620618522373 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209527421223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_29 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41534442594479 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276191430943 / 12500000000000 : ℝ))
      (E := (cell13058 ⟨29, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41534442594479 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (276191430943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_30 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41517350816413 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (220953543709 / 10000000000000 : ℝ))
      (E := (cell13058 ⟨30, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41517350816413 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (220953543709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_31 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (8300054191213 / 10000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (69048107807 / 3125000000000 : ℝ))
      (E := (cell13058 ⟨31, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (8300054191213 / 10000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (69048107807 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_32 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82966405995693 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209543486977 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨32, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82966405995693 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209543486977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_33 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (20733073463123 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209547490943 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨33, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (20733073463123 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209547490943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_34 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41449102725833 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104775760537 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨34, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41449102725833 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104775760537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_35 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82864140762507 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (69048609977 / 3125000000000 : ℝ))
      (E := (cell13058 ⟨35, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82864140762507 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (69048609977 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_36 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (16566019950893 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (138097471529 / 6250000000000 : ℝ))
      (E := (cell13058 ⟨36, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (16566019950893 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (138097471529 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_37 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82796082397143 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552390884519 / 25000000000000 : ℝ))
      (E := (cell13058 ⟨37, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82796082397143 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552390884519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_38 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82762088660299 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209567558653 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨38, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82762088660299 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209567558653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_39 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (82728118513843 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104785773553 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨39, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (82728118513843 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104785773553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13059_20 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83377600830023 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209382423961 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨20, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83377600830023 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209382423961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_21 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (20835800332881 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (220938641067 / 10000000000000 : ℝ))
      (E := (cell13059 ⟨21, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (20835800332881 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (220938641067 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_22 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41654412978179 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209390457617 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨22, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41654412978179 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209390457617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_23 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (20818618667969 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (110469722571 / 5000000000000 : ℝ))
      (E := (cell13059 ⟨23, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (20818618667969 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (110469722571 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_24 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83240147445597 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209398453491 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨24, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83240147445597 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209398453491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_25 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (16641168849041 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104701233339 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨25, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (16641168849041 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104701233339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_26 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83171565038549 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209406493593 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨26, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83171565038549 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209406493593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_27 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (20784327448411 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104705239069 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨27, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (20784327448411 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104705239069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_28 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83103078478667 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209414480893 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨28, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83103078478667 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209414480893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_29 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83068871061959 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (69044328243 / 3125000000000 : ℝ))
      (E := (cell13059 ⟨29, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83068871061959 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (69044328243 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_30 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (4151734375601 / 5000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209422548477 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨30, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (4151734375601 / 5000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209422548477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_31 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83000527797513 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (34522289967 / 1562500000000 : ℝ))
      (E := (cell13059 ⟨31, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83000527797513 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (34522289967 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_32 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41483195943629 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209430533173 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨32, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41483195943629 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209430533173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_33 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (16586455950047 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209434533887 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨33, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (16586455950047 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209434533887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_34 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41449095677791 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209438560811 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨34, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41449095677791 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209438560811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_35 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (8286412667259 / 10000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209442555841 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨35, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (8286412667259 / 10000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209442555841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_36 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (82830085670711 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209446577927 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨36, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (82830085670711 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209446577927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_37 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41398034159773 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209450627183 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨37, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41398034159773 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209450627183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_38 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41381037294427 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104727322381 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨38, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41381037294427 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104727322381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_39 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (16545620889709 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (276182328783 / 12500000000000 : ℝ))
      (E := (cell13059 ⟨39, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (16545620889709 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (276182328783 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13060_20 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83377586649221 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276158688563 / 12500000000000 : ℝ))
      (E := (cell13060 ⟨20, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83377586649221 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276158688563 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_21 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41671593578481 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209273549741 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨21, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41671593578481 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209273549741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_22 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83308811788031 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209277534589 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨22, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83308811788031 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209277534589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_23 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41637230254889 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (552320381169 / 25000000000000 : ℝ))
      (E := (cell13060 ⟨23, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41637230254889 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (552320381169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_24 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83240133289723 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441857116297 / 20000000000000 : ℝ))
      (E := (cell13060 ⟨24, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83240133289723 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441857116297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_25 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (1664116601911 / 2000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209289591073 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨25, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (1664116601911 / 2000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209289591073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_26 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83171550895107 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104646777991 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨26, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83171550895107 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104646777991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_27 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (8313729565641 / 10000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104648797737 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨27, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (8313729565641 / 10000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104648797737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_28 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (20775766086909 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209301594769 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨28, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (20775766086909 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209301594769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_29 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41534428468563 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104652807119 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨29, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41534428468563 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104652807119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_30 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (4151733669669 / 5000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (88372383881 / 4000000000000 : ℝ))
      (E := (cell13060 ⟨30, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (4151733669669 / 5000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (88372383881 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_31 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (4150025684253 / 5000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209313603091 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨31, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (4150025684253 / 5000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209313603091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_32 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82966377780987 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276164704209 / 12500000000000 : ℝ))
      (E := (cell13060 ⟨32, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82966377780987 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276164704209 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_33 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82932265650141 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209321631157 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨33, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82932265650141 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209321631157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_34 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82898177261659 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (22093256549 / 1000000000000 : ℝ))
      (E := (cell13060 ⟨34, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82898177261659 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (22093256549 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_35 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41432056292417 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104664852729 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨35, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41432056292417 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104664852729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_36 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (20707517897279 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209333665791 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨36, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (20707517897279 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209333665791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_37 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (20699013561027 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209337712003 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨37, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (20699013561027 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209337712003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_38 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (82762060519567 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104670863293 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨38, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (82762060519567 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104670863293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_39 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (16545618077081 / 20000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (138084106821 / 6250000000000 : ℝ))
      (E := (cell13060 ⟨39, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (16545618077081 / 20000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (138084106821 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13061_20 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (83377572470593 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (110457832353 / 5000000000000 : ℝ))
      (E := (cell13061 ⟨20, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (83377572470593 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (110457832353 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_21 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (83343172984573 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209160626177 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨21, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (83343172984573 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209160626177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_22 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (20827199405469 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209164665623 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨22, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (20827199405469 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209164665623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_23 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (20818611587463 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104584326009 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨23, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (20818611587463 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104584326009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_24 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (4162005956801 / 5000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276146580847 / 12500000000000 : ℝ))
      (E := (cell13061 ⟨24, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (4162005956801 / 5000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276146580847 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_25 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (2600181748377 / 3125000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104588326371 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨25, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (2600181748377 / 3125000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104588326371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_26 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41585768376917 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209180672529 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨26, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41585768376917 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209180672529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_27 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (1299020023771 / 1562500000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552296177129 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨27, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (1299020023771 / 1562500000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552296177129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_28 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (20775762554693 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (69037147011 / 3125000000000 : ℝ))
      (E := (cell13061 ⟨28, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (20775762554693 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (69037147011 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_29 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (83068842814459 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276149090051 / 12500000000000 : ℝ))
      (E := (cell13061 ⟨29, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (83068842814459 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276149090051 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_30 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (10379332409613 / 12500000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276149594797 / 12500000000000 : ℝ))
      (E := (cell13061 ⟨30, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (10379332409613 / 12500000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276149594797 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_31 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (8300049957477 / 10000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104600380573 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨31, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (8300049957477 / 10000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104600380573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_32 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41483181838439 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209204729883 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨32, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41483181838439 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209204729883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_33 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (5183265722013 / 6250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104604391379 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨33, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (5183265722013 / 6250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104604391379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_34 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (82898163169897 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209212803343 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨34, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (82898163169897 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209212803343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_35 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41432049249619 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (17673734337 / 800000000000 : ℝ))
      (E := (cell13061 ⟨35, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41432049249619 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (17673734337 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_36 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (1035375718871 / 1250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104610404029 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨36, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (1035375718871 / 1250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104610404029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_37 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (20699010042707 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209224792539 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨37, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (20699010042707 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209224792539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_38 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (82762046452437 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104614402063 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨38, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (82762046452437 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104614402063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_39 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (4136403816221 / 5000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552308210621 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨39, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (4136403816221 / 5000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552308210621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13062_20 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83377558294139 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104521890659 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨20, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83377558294139 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104521890659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_21 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83343158814357 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (44180955133 / 2000000000000 : ℝ))
      (E := (cell13062 ⟨21, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83343158814357 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (44180955133 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_22 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (20827195864473 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209051792361 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨22, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (20827195864473 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209051792361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_23 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (2602326006003 / 3125000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (441811155013 / 20000000000000 : ℝ))
      (E := (cell13062 ⟨23, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (2602326006003 / 3125000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (441811155013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_24 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41620052492243 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104529912293 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨24, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41620052492243 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104529912293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_25 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83205801802747 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104531913489 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨25, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83205801802747 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104531913489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_26 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83171522614729 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552266960809 / 25000000000000 : ℝ))
      (E := (cell13062 ⟨26, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83171522614729 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552266960809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_27 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (16627453477689 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (441814363453 / 20000000000000 : ℝ))
      (E := (cell13062 ⟨27, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (16627453477689 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (441814363453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_28 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41551518046037 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209075868143 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨28, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41551518046037 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209075868143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_29 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (20767207173489 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209079880811 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨29, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (20767207173489 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209079880811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_30 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (2594832661331 / 3125000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (220908385689 / 10000000000000 : ℝ))
      (E := (cell13062 ⟨30, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (2594832661331 / 3125000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (220908385689 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_31 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (20750121366661 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209087856341 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨31, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (20750121366661 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209087856341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_32 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (20741587393733 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209091880399 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨32, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (20741587393733 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209091880399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_33 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82932237456437 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209095930071 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨33, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82932237456437 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209095930071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_34 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (10362268635037 / 12500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104549973749 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨34, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (10362268635037 / 12500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104549973749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_35 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82864084415801 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209103933171 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨35, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82864084415801 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209103933171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_36 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82830043432403 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209107946039 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨36, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82830043432403 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209107946039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_37 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (16559205219941 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104555963751 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨37, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (16559205219941 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104555963751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_38 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (10345254048433 / 12500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209115994851 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨38, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (10345254048433 / 12500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209115994851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_39 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (82728062265591 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209119971549 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨39, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (82728062265591 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209119971549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13063_20 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41688772059929 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208930911277 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨20, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41688772059929 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208930911277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_21 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83343144646313 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208934941163 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨21, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83343144646313 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208934941163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_22 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (1041359616201 / 1250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208938973161 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨22, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (1041359616201 / 1250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208938973161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_23 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83274418036511 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104471476099 / 50000000000000 : ℝ))
      (E := (cell13063 ⟨23, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83274418036511 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104471476099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_24 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41620045417561 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208946939693 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨24, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41620045417561 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208946939693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_25 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83205787659599 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104475498459 / 50000000000000 : ℝ))
      (E := (cell13063 ⟨25, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83205787659599 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104475498459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_26 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83171508477791 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208955009651 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨26, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83171508477791 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208955009651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_27 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83137253257713 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208958980199 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨27, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83137253257713 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208958980199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_28 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41551510983771 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208963027643 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨28, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41551510983771 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208963027643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_29 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83068814575619 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208967036923 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨29, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83068814575619 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208967036923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_30 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20758657762611 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208971009661 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨30, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20758657762611 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208971009661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_31 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (2075011784017 / 2500000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552243766097 / 25000000000000 : ℝ))
      (E := (cell13063 ⟨31, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (2075011784017 / 2500000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552243766097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_32 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20741583868787 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (110448954261 / 5000000000000 : ℝ))
      (E := (cell13063 ⟨32, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20741583868787 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (110448954261 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_33 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82932223362827 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (276122884137 / 12500000000000 : ℝ))
      (E := (cell13063 ⟨33, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82932223362827 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (276122884137 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_34 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41449067496427 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208987087369 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨34, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41449067496427 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208987087369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_35 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20716017583631 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (220899106993 / 10000000000000 : ℝ))
      (E := (cell13063 ⟨35, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20716017583631 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (220899106993 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_36 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20707507339321 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441799015947 / 20000000000000 : ℝ))
      (E := (cell13063 ⟨36, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20707507339321 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441799015947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_37 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82796012030739 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208999116893 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨37, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82796012030739 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208999116893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_38 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82762018324647 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209003122559 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨38, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82762018324647 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209003122559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_39 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (82728048208917 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209007155091 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨39, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (82728048208917 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2209007155091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13064_20 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (333510119791 / 400000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208818095253 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨20, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (333510119791 / 400000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208818095253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_21 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83343130480441 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104411060691 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨21, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83343130480441 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104411060691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_22 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83308755136439 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208826149667 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨22, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83308755136439 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208826149667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_23 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16654880776619 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (27610376563 / 1250000000000 : ℝ))
      (E := (cell13064 ⟨23, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16654880776619 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (27610376563 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_24 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83240076687927 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104417083661 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨24, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83240076687927 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104417083661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_25 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41602886759309 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208838162569 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨25, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41602886759309 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208838162569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_26 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (4158574717151 / 5000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (88353686871 / 4000000000000 : ℝ))
      (E := (cell13064 ⟨26, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (4158574717151 / 5000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (88353686871 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_27 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41568619564573 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208846197321 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨27, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41568619564573 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208846197321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_28 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (3324120313807 / 4000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104425091427 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨28, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (3324120313807 / 4000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104425091427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_29 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16613760091889 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208854188749 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨29, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16613760091889 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208854188749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_30 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83034616940459 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208858216693 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨30, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83034616940459 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208858216693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_31 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83000457256879 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104431104789 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨31, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83000457256879 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104431104789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_32 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (3318652855101 / 4000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208866227163 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨32, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (3318652855101 / 4000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208866227163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_33 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (82932209271377 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441774054091 / 20000000000000 : ℝ))
      (E := (cell13064 ⟨33, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (82932209271377 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441774054091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_34 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (20724530226893 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (552218570399 / 25000000000000 : ℝ))
      (E := (cell13064 ⟨34, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (20724530226893 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (552218570399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_35 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (20716014063851 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208878261073 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨35, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (20716014063851 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208878261073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_36 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (82830015284323 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208882267837 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨36, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (82830015284323 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208882267837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_37 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (8279599796393 / 10000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208886302003 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨37, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (8279599796393 / 10000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208886302003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_38 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16552400852797 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208890304723 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨38, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16552400852797 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208890304723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_39 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41364017077199 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104447167177 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨39, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41364017077199 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104447167177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13065_20 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41688757888907 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104352666623 / 50000000000000 : ℝ))
      (E := (cell13065 ⟨20, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41688757888907 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104352666623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_21 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (4167155815837 / 5000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276088662163 / 12500000000000 : ℝ))
      (E := (cell13065 ⟨21, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (4167155815837 / 5000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276088662163 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_22 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (10413592622371 / 12500000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208713321879 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨22, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (10413592622371 / 12500000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208713321879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_23 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83274389731849 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (220871735197 / 10000000000000 : ℝ))
      (E := (cell13065 ⟨23, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83274389731849 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (220871735197 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_24 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (832400625429 / 1000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208721332251 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨24, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (832400625429 / 1000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208721332251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_25 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (16641151875961 / 20000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208725382357 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨25, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (16641151875961 / 20000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208725382357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_26 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (5198217513151 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208729388061 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨26, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (5198217513151 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208729388061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_27 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41568612501373 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208733410151 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨27, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41568612501373 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208733410151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_28 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (20775748431243 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208737392277 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨28, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (20775748431243 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208737392277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_29 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (20767196586359 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276092674351 / 12500000000000 : ℝ))
      (E := (cell13065 ⟨29, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (20767196586359 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276092674351 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_30 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83034602832637 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208745419437 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨30, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83034602832637 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208745419437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_31 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83000443155239 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208749409053 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨31, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83000443155239 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208749409053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_32 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82966307282063 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104376711707 / 50000000000000 : ℝ))
      (E := (cell13065 ⟨32, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82966307282063 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104376711707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_33 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82932195182087 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208757463529 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨33, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82932195182087 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208757463529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_34 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82898106824449 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208761471539 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨34, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82898106824449 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208761471539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_35 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82864042178443 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (552191376649 / 25000000000000 : ℝ))
      (E := (cell13065 ⟨35, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82864042178443 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (552191376649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_36 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41415000606759 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208769510347 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨36, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41415000606759 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208769510347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_37 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82795983899277 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (138048342677 / 6250000000000 : ℝ))
      (E := (cell13065 ⟨37, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82795983899277 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (138048342677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_38 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82761990205479 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (110438877067 / 5000000000000 : ℝ))
      (E := (cell13065 ⟨38, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82761990205479 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (110438877067 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_39 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (82728020102033 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208781509337 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨39, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (82728020102033 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208781509337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13066_20 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83377501610049 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208592508631 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨20, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83377501610049 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208592508631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_21 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (8334310215521 / 10000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208596527269 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨21, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (8334310215521 / 10000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208596527269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_22 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83308726823667 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208600548157 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨22, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83308726823667 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208600548157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_23 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20818593895693 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (138037785913 / 6250000000000 : ℝ))
      (E := (cell13066 ⟨23, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20818593895693 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (138037785913 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_24 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83240048400041 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (441721710259 / 20000000000000 : ℝ))
      (E := (cell13066 ⟨24, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83240048400041 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (441721710259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_25 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83205745243159 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104306298927 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨25, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83205745243159 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104306298927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_26 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (41585733039989 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208616600057 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨26, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (41585733039989 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208616600057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_27 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (8313721087851 / 10000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104310309347 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨27, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (8313721087851 / 10000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104310309347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_28 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (41551489803467 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (220862459741 / 10000000000000 : ℝ))
      (E := (cell13066 ⟨28, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (41551489803467 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (220862459741 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_29 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83068772233589 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (441725731021 / 20000000000000 : ℝ))
      (E := (cell13066 ⟨29, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83068772233589 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (441725731021 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_30 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83034588726977 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (441726523579 / 20000000000000 : ℝ))
      (E := (cell13066 ⟨30, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83034588726977 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (441726523579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_31 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83000429055761 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208636662813 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨31, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83000429055761 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208636662813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_32 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82966293188761 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (88345626959 / 4000000000000 : ℝ))
      (E := (cell13066 ⟨32, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82966293188761 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (88345626959 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_33 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20733045273739 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (13804029077 / 625000000000 : ℝ))
      (E := (cell13066 ⟨33, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20733045273739 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (13804029077 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_34 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20724523185871 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208648715841 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨34, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20724523185871 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208648715841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_35 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82864028103639 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208652689173 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨35, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82864028103639 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208652689173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_36 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (8282998714487 / 10000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104328344943 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨36, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (8282998714487 / 10000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104328344943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_37 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (4139798491839 / 5000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208660718091 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨37, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (4139798491839 / 5000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208660718091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_38 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (82761976149127 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (34510386171 / 1562500000000 : ℝ))
      (E := (cell13066 ⟨38, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (82761976149127 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (34510386171 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_39 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (41364003025911 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208668738799 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨39, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (41364003025911 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208668738799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13067_20 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (10422185930557 / 12500000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (44169595927 / 2000000000000 : ℝ))
      (E := (cell13067 ⟨20, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (10422185930557 / 12500000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (44169595927 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_21 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (1666861759917 / 2000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208483811279 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨21, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (1666861759917 / 2000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208483811279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_22 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (10413589083817 / 12500000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276060978563 / 12500000000000 : ℝ))
      (E := (cell13067 ⟨22, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (10413589083817 / 12500000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276060978563 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_23 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83274361435863 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441698358591 / 20000000000000 : ℝ))
      (E := (cell13067 ⟨23, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83274361435863 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441698358591 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_24 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83240034259349 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208495824457 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨24, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83240034259349 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208495824457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_25 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (2080143277717 / 2500000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104249904531 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨25, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (2080143277717 / 2500000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104249904531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_26 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (16634290390341 / 20000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (110425193311 / 5000000000000 : ℝ))
      (E := (cell13067 ⟨26, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (16634290390341 / 20000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (110425193311 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_27 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83137196756439 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104253940713 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨27, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83137196756439 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104253940713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_28 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83102965491059 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208511856759 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨28, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83102965491059 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208511856759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_29 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (16613751624781 / 20000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208515852593 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨29, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (16613751624781 / 20000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208515852593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_30 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83034574623479 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276064983827 / 12500000000000 : ℝ))
      (E := (cell13067 ⟨30, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83034574623479 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276064983827 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_31 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83000414958443 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208523912289 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨31, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83000414958443 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208523912289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_32 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41483139548809 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104263960127 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨32, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41483139548809 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104263960127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_33 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (1295815109531 / 1562500000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (138033247129 / 6250000000000 : ℝ))
      (E := (cell13067 ⟨33, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (1295815109531 / 1562500000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (138033247129 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_34 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41449039332339 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208535955861 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨34, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41449039332339 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208535955861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_35 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (5179000876937 / 6250000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441707985227 / 20000000000000 : ℝ))
      (E := (cell13067 ⟨35, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (5179000876937 / 6250000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441707985227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_36 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41414986539189 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104271991261 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨36, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41414986539189 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104271991261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_37 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41397977888219 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (138034246817 / 6250000000000 : ℝ))
      (E := (cell13067 ⟨37, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41397977888219 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (138034246817 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_38 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (8276196209493 / 10000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208552001739 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨38, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (8276196209493 / 10000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208552001739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_39 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (20681998000941 / 25000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276069502843 / 12500000000000 : ℝ))
      (E := (cell13067 ⟨39, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (20681998000941 / 25000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276069502843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13068_20 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41688736640517 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104183510731 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨20, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41688736640517 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104183510731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_21 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83343073838661 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208371032659 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨21, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83343073838661 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208371032659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_22 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83308698519573 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (11041875231 / 500000000000 : ℝ))
      (E := (cell13068 ⟨22, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83308698519573 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (11041875231 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_23 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83274347291121 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104189532699 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨23, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83274347291121 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104189532699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_24 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (10405002515103 / 12500000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208383093331 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨24, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (10405002515103 / 12500000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208383093331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_25 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41602858488183 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208387074413 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨25, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41602858488183 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208387074413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_26 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83171437825597 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (69012222753 / 3125000000000 : ℝ))
      (E := (cell13068 ⟨26, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83171437825597 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (69012222753 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_27 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83137182636531 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208395139873 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨27, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83137182636531 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208395139873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_28 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83102951377347 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208399111823 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨28, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83102951377347 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208399111823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_29 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83068744016383 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (552100790711 / 25000000000000 : ℝ))
      (E := (cell13068 ⟨29, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83068744016383 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (552100790711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_30 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41517280261071 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208407177601 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨30, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41517280261071 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208407177601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_31 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41500200431643 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208411157483 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨31, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41500200431643 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208411157483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_32 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (20741566252159 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208415162249 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨32, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (20741566252159 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208415162249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_33 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (82932152927171 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208419192909 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨33, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (82932152927171 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208419192909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_34 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (20724516147007 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104211595801 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨34, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (20724516147007 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104211595801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_35 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41431999980251 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208427217481 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨35, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41431999980251 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208427217481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_36 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (82829959014041 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208431212193 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨36, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (82829959014041 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208431212193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_37 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (331183766873 / 400000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (276054404311 / 12500000000000 : ℝ))
      (E := (cell13068 ⟨37, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (331183766873 / 400000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (276054404311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_38 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41380974021443 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104219642129 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨38, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41380974021443 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104219642129 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_39 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41363988978929 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (441688648731 / 20000000000000 : ℝ))
      (E := (cell13068 ⟨39, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41363988978929 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (441688648731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13069_20 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83377459119781 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (220825435891 / 10000000000000 : ℝ))
      (E := (cell13069 ⟨20, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83377459119781 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (220825435891 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_21 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (2083576492091 / 2500000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208258366423 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨21, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (2083576492091 / 2500000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208258366423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_22 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41654342185389 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208262376327 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨22, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41654342185389 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208262376327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_23 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (20818583287137 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208266391933 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨23, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (20818583287137 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208266391933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_24 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41620002992233 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441654071583 / 20000000000000 : ℝ))
      (E := (cell13069 ⟨24, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41620002992233 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441654071583 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_25 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41602851423109 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208274393907 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨25, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41602851423109 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208274393907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_26 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41585711850827 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552069596421 / 25000000000000 : ℝ))
      (E := (cell13069 ⟨26, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41585711850827 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552069596421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_27 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (20784292129697 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208282394033 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨27, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (20784292129697 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208282394033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_28 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83102937265797 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208286421103 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨28, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83102937265797 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208286421103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_29 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83068729911023 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208290410287 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨29, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83068729911023 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208290410287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_30 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41517273211483 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441658884351 / 20000000000000 : ℝ))
      (E := (cell13069 ⟨30, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41517273211483 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441658884351 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_31 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (5187524173143 / 6250000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104149228483 / 50000000000000 : ℝ))
      (E := (cell13069 ⟨31, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (5187524173143 / 6250000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104149228483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_32 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (82966250921811 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (6900945183 / 312500000000 : ℝ))
      (E := (cell13069 ⟨32, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (82966250921811 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (6900945183 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_33 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (16586427769303 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552076621523 / 25000000000000 : ℝ))
      (E := (cell13069 ⟨33, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (16586427769303 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552076621523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_34 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (647641019637 / 781250000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (276038810213 / 12500000000000 : ℝ))
      (E := (cell13069 ⟨34, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (647641019637 / 781250000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (276038810213 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_35 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (10357998236521 / 12500000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208314504549 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨35, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (10357998236521 / 12500000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208314504549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_36 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (4141497247593 / 5000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208318496273 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨36, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (4141497247593 / 5000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208318496273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_37 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (10349490957777 / 12500000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208322515627 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨37, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (10349490957777 / 12500000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208322515627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_38 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (16552386798599 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104163281251 / 50000000000000 : ℝ))
      (E := (cell13069 ⟨38, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (16552386798599 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104163281251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_39 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (16545592782821 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (138020661113 / 6250000000000 : ℝ))
      (E := (cell13069 ⟨39, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (16545592782821 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (138020661113 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13070_20 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83377444960699 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208141633753 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨20, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83377444960699 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208141633753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_21 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (20835761382697 / 25000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208145637561 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨21, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (20835761382697 / 25000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208145637561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_22 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (10413583778019 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (552037425541 / 25000000000000 : ℝ))
      (E := (cell13070 ⟨22, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (10413583778019 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (552037425541 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_23 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83274319008141 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104076827899 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨23, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83274319008141 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104076827899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_24 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41619995925137 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (110407883831 / 5000000000000 : ℝ))
      (E := (cell13070 ⟨24, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41619995925137 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (110407883831 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_25 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (16641137743647 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (552040427279 / 25000000000000 : ℝ))
      (E := (cell13070 ⟨25, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (16641137743647 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (552040427279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_26 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (665371276639 / 800000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104082848721 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨26, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (665371276639 / 800000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104082848721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_27 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83137154403207 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208169702387 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨27, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83137154403207 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208169702387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_28 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (8310292315641 / 10000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208173726099 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨28, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (8310292315641 / 10000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208173726099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_29 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (5191794737989 / 6250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208177770497 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨29, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (5191794737989 / 6250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208177770497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_30 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (1660690646519 / 2000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208181778723 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨30, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (1660690646519 / 2000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208181778723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_31 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (1660007453589 / 2000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208185752167 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨31, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (1660007453589 / 2000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208185752167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_32 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41483118418573 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208189809183 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨32, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41483118418573 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208189809183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_33 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (5183257798001 / 6250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (552048443749 / 25000000000000 : ℝ))
      (E := (cell13070 ⟨33, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (5183257798001 / 6250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (552048443749 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_34 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (207245091103 / 250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (220819782617 / 10000000000000 : ℝ))
      (E := (cell13070 ⟨34, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (207245091103 / 250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (220819782617 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_35 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82863971825989 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441640369201 / 20000000000000 : ℝ))
      (E := (cell13070 ⟨35, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82863971825989 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441640369201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_36 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82829930891833 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441641166953 / 20000000000000 : ℝ))
      (E := (cell13070 ⟨36, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82829930891833 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441641166953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_37 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (5174744600521 / 6250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208209851203 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨37, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (5174744600521 / 6250000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208209851203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_38 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (82761919945257 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (220821383647 / 10000000000000 : ℝ))
      (E := (cell13070 ⟨38, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (82761919945257 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (220821383647 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_39 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (10340993734063 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (69006807779 / 3125000000000 : ℝ))
      (E := (cell13070 ⟨39, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (10340993734063 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (69006807779 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13071_20 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41688715401893 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208028962621 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨20, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41688715401893 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208028962621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_21 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (10417878922513 / 12500000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552008255271 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨21, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (10417878922513 / 12500000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552008255271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_22 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (20827164019923 / 25000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441607404743 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨22, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (20827164019923 / 25000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441607404743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_23 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (832743048699 / 1000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (138002564509 / 6250000000000 : ℝ))
      (E := (cell13071 ⟨23, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (832743048699 / 1000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (138002564509 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_24 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (83239977718247 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104022524723 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨24, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (83239977718247 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104022524723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_25 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (2600177331013 / 3125000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208049020039 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨25, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (2600177331013 / 3125000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208049020039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_26 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (83171395460259 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (220805306337 / 10000000000000 : ℝ))
      (E := (cell13071 ⟨26, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (83171395460259 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (220805306337 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_27 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (83137140289789 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441611412987 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨27, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (83137140289789 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441611412987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_28 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (2596965907787 / 3125000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441612217063 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨28, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (2596965907787 / 3125000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441612217063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_29 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (16613740341357 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208065067901 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨29, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (16613740341357 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208065067901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_30 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41517259115547 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104034536431 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨30, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41517259115547 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104034536431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_31 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (83000358590771 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (110403655083 / 5000000000000 : ℝ))
      (E := (cell13071 ⟨31, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (83000358590771 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (110403655083 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_32 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41483111377319 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104038548467 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨32, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41483111377319 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104038548467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_33 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (3317284427667 / 4000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (13800506989 / 625000000000 : ℝ))
      (E := (cell13071 ⟨33, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (3317284427667 / 4000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (13800506989 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_34 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82898022371019 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (55202129159 / 2500000000000 : ℝ))
      (E := (cell13071 ⟨34, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82898022371019 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (55202129159 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_35 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (16572791552393 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441617836637 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨35, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (16572791552393 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441617836637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_36 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (2070747920849 / 2500000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104046584491 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨36, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (2070747920849 / 2500000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1104046584491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_37 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82795899556609 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208097182503 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨37, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82795899556609 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208097182503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_38 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (82761905899671 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552025305909 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨38, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (82761905899671 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552025305909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_39 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41363967916527 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552026308323 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨39, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41363967916527 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (552026308323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13072_20 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83377416649041 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (441583269103 / 20000000000000 : ℝ))
      (E := (cell13072 ⟨20, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83377416649041 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (441583269103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_21 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (20835754307897 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207920341983 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨21, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (20835754307897 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207920341983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_22 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83308641937399 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (110396217049 / 5000000000000 : ℝ))
      (E := (cell13072 ⟨22, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83308641937399 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (110396217049 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_23 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (3330971629353 / 4000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (551982101051 / 25000000000000 : ℝ))
      (E := (cell13072 ⟨23, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (3330971629353 / 4000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (551982101051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_24 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (16647992717677 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207932359581 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨24, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (16647992717677 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207932359581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_25 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83205660468761 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207936385109 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨25, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83205660468761 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207936385109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_26 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (41585690671403 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (441588085003 / 20000000000000 : ℝ))
      (E := (cell13072 ⟨26, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (41585690671403 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (441588085003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_27 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83137126178533 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103972211601 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨27, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83137126178533 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103972211601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_28 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (2077572373603 / 2500000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (275993555031 / 12500000000000 : ℝ))
      (E := (cell13072 ⟨28, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (2077572373603 / 2500000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (275993555031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_29 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83068687607907 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207952419549 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨29, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83068687607907 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207952419549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_30 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (20758626034599 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207956479819 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨30, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (20758626034599 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207956479819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_31 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83000344504249 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (551990111719 / 25000000000000 : ℝ))
      (E := (cell13072 ⟨31, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83000344504249 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (551990111719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_32 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82966208674287 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207964497597 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨32, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82966208674287 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207964497597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_33 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (8293209661749 / 10000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (88318740633 / 4000000000000 : ℝ))
      (E := (cell13072 ⟨33, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (8293209661749 / 10000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (88318740633 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_34 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (16579601660599 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (8624892587 / 390625000000 : ℝ))
      (E := (cell13072 ⟨34, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (16579601660599 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (8624892587 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_35 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (16572788740019 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207976516091 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨35, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (16572788740019 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207976516091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_36 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (82829902778241 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103990278807 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨36, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (82829902778241 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103990278807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_37 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (16559177101407 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103992284121 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨37, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (16559177101407 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103992284121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_38 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (20690472964059 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103994273897 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨38, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (20690472964059 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103994273897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_39 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (41363960897877 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (551998138657 / 25000000000000 : ℝ))
      (E := (cell13072 ⟨39, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (41363960897877 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (551998138657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13073_20 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (16675480499293 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207803724121 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨20, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (16675480499293 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207803724121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_21 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (2083575077131 / 2500000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207807716931 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨21, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (2083575077131 / 2500000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207807716931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_22 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83308627797273 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207811770679 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨22, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83308627797273 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207811770679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_23 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (20818569149979 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207815771979 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨23, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (20818569149979 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207815771979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_24 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83239949460687 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103909891123 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨24, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83239949460687 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103909891123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_25 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (8320564634727 / 10000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207823804327 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨25, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (8320564634727 / 10000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207823804327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_26 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (20792841806879 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103913891189 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨26, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (20792841806879 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103913891189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_27 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83137112069439 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103915888593 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨27, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83137112069439 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103915888593 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_28 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (162310314143 / 195312500000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103917895451 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨28, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (162310314143 / 195312500000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103917895451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_29 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83068673511189 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207839825441 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨29, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83068673511189 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207839825441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_30 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41517245023929 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551960955987 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨30, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41517245023929 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551960955987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_31 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41500165209943 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (137990490399 / 6250000000000 : ℝ))
      (E := (cell13073 ⟨31, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41500165209943 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (137990490399 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_32 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82966194596093 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207851835389 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨32, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82966194596093 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207851835389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_33 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82932082545461 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551963962629 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨33, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82932082545461 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551963962629 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_34 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (663183953897 / 800000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (275982486569 / 12500000000000 : ℝ))
      (E := (cell13073 ⟨34, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (663183953897 / 800000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (275982486569 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_35 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (4143196482019 / 5000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103931951693 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨35, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (4143196482019 / 5000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103931951693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_36 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41414944362337 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551966970821 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨36, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41414944362337 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551966970821 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_37 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82795871459613 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207871949709 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨37, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82795871459613 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207871949709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_38 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (82761877814953 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (137992245401 / 6250000000000 : ℝ))
      (E := (cell13073 ⟨38, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (82761877814953 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (137992245401 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_39 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (16545581552121 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (44157598609 / 2000000000000 : ℝ))
      (E := (cell13073 ⟨39, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (16545581552121 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (44157598609 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13074_20 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (10422173543257 / 12500000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207691098441 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨20, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (10422173543257 / 12500000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207691098441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_21 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41671494470529 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551923786483 / 25000000000000 : ℝ))
      (E := (cell13074 ⟨21, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41671494470529 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551923786483 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_22 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (83308613659313 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207699137733 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨22, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (83308613659313 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207699137733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_23 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20818565617043 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207703135469 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨23, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20818565617043 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207703135469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_24 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (83239935335153 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207707142221 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨24, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (83239935335153 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207707142221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_25 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41602816113971 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207711160831 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨25, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41602816113971 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207711160831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_26 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20792838278597 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207715193913 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨26, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20792838278597 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207715193913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_27 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (16627419592501 / 20000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207719185369 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨27, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (16627419592501 / 20000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207719185369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_28 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (10387858342559 / 12500000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207723195777 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨28, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (10387858342559 / 12500000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207723195777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_29 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (83068659416629 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (137982951691 / 6250000000000 : ℝ))
      (E := (cell13074 ⟨29, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (83068659416629 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (137982951691 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_30 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41517237979739 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207731222347 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨30, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41517237979739 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207731222347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_31 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (83000316337679 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (137983452601 / 6250000000000 : ℝ))
      (E := (cell13074 ⟨31, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (83000316337679 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (137983452601 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_32 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (10370772565007 / 12500000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207739286093 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨32, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (10370772565007 / 12500000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207739286093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_33 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82932068475587 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207743298169 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨33, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82932068475587 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207743298169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_34 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82897980173409 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207747278557 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨34, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82897980173409 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207747278557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_35 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41431957791409 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275968910801 / 12500000000000 : ℝ))
      (E := (cell13074 ⟨35, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41431957791409 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275968910801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_36 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (82829874673261 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207755322057 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨36, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (82829874673261 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207755322057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_37 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41397928707171 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275969915863 / 12500000000000 : ℝ))
      (E := (cell13074 ⟨37, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41397928707171 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275969915863 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_38 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (4138093188791 / 5000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207763359503 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨38, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (4138093188791 / 5000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207763359503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_39 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (16545578745521 / 20000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103883680381 / 50000000000000 : ℝ))
      (E := (cell13074 ⟨39, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (16545578745521 / 20000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103883680381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

end BstLean.Part268
