import BstLean.Part268CellShard22Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12900_20 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83379456517197 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (89105241021 / 4000000000000 : ℝ))
      (E := (cell12900 ⟨20, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83379456517197 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (89105241021 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_21 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83345034975763 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227635057979 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨21, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83345034975763 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227635057979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_22 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83310637588047 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113819519031 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨22, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83310637588047 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113819519031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_23 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41638132160669 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227643085883 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨23, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41638132160669 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227643085883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_24 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83241915143093 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227647087937 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨24, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83241915143093 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227647087937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_25 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (10400948752617 / 12500000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113825523563 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨25, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (10400948752617 / 12500000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113825523563 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_26 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83173288922657 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113827541499 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨26, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83173288922657 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113827541499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_27 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (8313901181621 / 10000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113829540603 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨27, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (8313901181621 / 10000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113829540603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_28 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83104758669713 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113831551221 / 50000000000000 : ℝ))
      (E := (cell12900 ⟨28, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83104758669713 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (1113831551221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_29 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83070529451447 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227667090243 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨29, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83070529451447 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227667090243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_30 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41518162064927 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (278458888111 / 12500000000000 : ℝ))
      (E := (cell12900 ⟨30, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41518162064927 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (278458888111 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_31 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (83002142673539 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227675089407 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨31, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (83002142673539 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227675089407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_32 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (16593597010253 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (222767910367 / 10000000000000 : ℝ))
      (E := (cell12900 ⟨32, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (16593597010253 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (222767910367 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_33 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82933851231953 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (222768309021 / 10000000000000 : ℝ))
      (E := (cell12900 ⟨33, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82933851231953 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (222768309021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_34 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (20724935296171 / 25000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227687108487 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨34, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (20724935296171 / 25000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227687108487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_35 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (16573130975739 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (139230697449 / 6250000000000 : ℝ))
      (E := (cell12900 ⟨35, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (16573130975739 / 20000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (139230697449 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_36 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41415796141689 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227695125417 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨36, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41415796141689 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227695125417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_37 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (82797553368281 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227699124671 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨37, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (82797553368281 / 100000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227699124671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_38 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (41381769051553 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227703156961 / 100000000000000 : ℝ))
      (E := (cell12900 ⟨38, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (41381769051553 / 50000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (2227703156961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12900_39 : CellCertificate 12900 (881186366739227 / 10000000000000000 : ℝ) (1628241987027163 / 1000000000000000000 : ℝ) (328775584106231 / 10000000000000000 : ℝ)
    (cell12900 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · norm_num [cell12900]
  · have h := gap_lower (n := 12900) (a := (20682386614427 / 25000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445541432667 / 20000000000000 : ℝ))
      (E := (cell12900 ⟨39, by decide⟩).energy) (xi := (328775584106231 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12900 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12900]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12900])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12900) (a := (20682386614427 / 25000000000000 : ℝ)) (b := (9977803371 / 6250000000000 : ℝ)) (q := (445541432667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12900])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12900]

theorem cert12901_20 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41689724010349 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227514343583 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨20, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41689724010349 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227514343583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_21 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83345026783033 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113759154297 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨21, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83345026783033 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113759154297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_22 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (10413828712333 / 12500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227522338573 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨22, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (10413828712333 / 12500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227522338573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_23 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83276256734879 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (22275263203 / 1000000000000 : ℝ))
      (E := (cell12901 ⟨23, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83276256734879 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (22275263203 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_24 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41620953929569 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227530373691 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨24, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41620953929569 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227530373691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_25 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (10400947879883 / 12500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113767163273 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨25, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (10400947879883 / 12500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113767163273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_26 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (5198330140153 / 6250000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113769178389 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨26, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (5198330140153 / 6250000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113769178389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_27 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (41569502718623 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227542350041 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨27, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (41569502718623 / 50000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227542350041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_28 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (3324190103663 / 4000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113773183513 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨28, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (3324190103663 / 4000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113773183513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_29 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83070523673719 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227550351267 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨29, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83070523673719 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227550351267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_30 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (2075907966303 / 2500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556888590761 / 25000000000000 : ℝ))
      (E := (cell12901 ⟨30, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (2075907966303 / 2500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556888590761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_31 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (83002137495383 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113779201971 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨31, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (83002137495383 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113779201971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_32 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (5185498760767 / 6250000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227562416743 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨32, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (5185498760767 / 6250000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227562416743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_33 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (8293384665171 / 10000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227566402509 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨33, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (8293384665171 / 10000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227566402509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_34 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82899736902777 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113785210351 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨34, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82899736902777 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113785210351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_35 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (10358206361839 / 12500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113787206677 / 50000000000000 : ℝ))
      (E := (cell12901 ⟨35, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (10358206361839 / 12500000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (1113787206677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_36 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82831588596907 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227578439527 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨36, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82831588596907 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227578439527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_37 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (2587423436841 / 3125000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227582440759 / 100000000000000 : ℝ))
      (E := (cell12901 ⟨37, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (2587423436841 / 3125000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (2227582440759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_38 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82763535010429 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (69612075531 / 3125000000000 : ℝ))
      (E := (cell12901 ⟨38, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82763535010429 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (69612075531 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12901_39 : CellCertificate 12901 (44057962859889 / 500000000000000 : ℝ) (1628115735651347 / 1000000000000000000 : ℝ) (328749497688749 / 10000000000000000 : ℝ)
    (cell12901 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · norm_num [cell12901]
  · have h := gap_lower (n := 12901) (a := (82729543661313 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556897606673 / 25000000000000 : ℝ))
      (E := (cell12901 ⟨39, by decide⟩).energy) (xi := (328749497688749 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12901 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12901]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12901])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12901) (a := (82729543661313 / 100000000000000 : ℝ)) (b := (39908083297 / 25000000000000 : ℝ)) (q := (556897606673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12901])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12901]

theorem cert12902_20 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83379439525737 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227397657907 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨20, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83379439525737 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227397657907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_21 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (16669003718361 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227401613833 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨21, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (16669003718361 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227401613833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_22 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (41655310905373 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113702817713 / 50000000000000 : ℝ))
      (E := (cell12902 ⟨22, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (41655310905373 / 50000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113702817713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_23 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (1665524982997 / 2000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (222740966783 / 10000000000000 : ℝ))
      (E := (cell12902 ⟨23, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (1665524982997 / 2000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (222740966783 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_24 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (1300654696509 / 1562500000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (111370682793 / 5000000000000 : ℝ))
      (E := (cell12902 ⟨24, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (1300654696509 / 1562500000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (111370682793 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_25 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83207576058549 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (69606801901 / 3125000000000 : ℝ))
      (E := (cell12902 ⟨25, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83207576058549 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (69606801901 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_26 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83173275563561 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445484337097 / 20000000000000 : ℝ))
      (E := (cell12902 ⟨26, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83173275563561 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445484337097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_27 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83138999059567 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227425673863 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨27, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83138999059567 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227425673863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_28 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83104746514687 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (17401794427 / 781250000000 : ℝ))
      (E := (cell12902 ⟨28, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83104746514687 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (17401794427 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_29 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (16614103579441 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113716833699 / 50000000000000 : ℝ))
      (E := (cell12902 ⟨29, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (16614103579441 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113716833699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_30 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (20759078293891 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227437676367 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨30, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (20759078293891 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227437676367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_31 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (83002132318369 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227441715149 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨31, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (83002132318369 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227441715149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_32 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (16593595058877 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (89097829061 / 4000000000000 : ℝ))
      (E := (cell12902 ⟨32, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (16593595058877 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (89097829061 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_33 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82933842072537 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227449711553 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨33, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82933842072537 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227449711553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_34 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (16579946524381 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113726864849 / 50000000000000 : ℝ))
      (E := (cell12902 ⟨34, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (16579946524381 / 20000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (1113726864849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_35 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (5179102931983 / 6250000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227457722991 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨35, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (5179102931983 / 6250000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227457722991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_36 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (414157924557 / 500000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227461750491 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨36, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (414157924557 / 500000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227461750491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_37 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (82797546590471 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227465753737 / 100000000000000 : ℝ))
      (E := (cell12902 ⟨37, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (82797546590471 / 100000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (2227465753737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_38 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (20690882979661 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (222746973267 / 10000000000000 : ℝ))
      (E := (cell12902 ⟨38, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (20690882979661 / 25000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (222746973267 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12902_39 : CellCertificate 12902 (220283037921263 / 2500000000000000 : ℝ) (1627989503852687 / 1000000000000000000 : ℝ) (328723415452673 / 10000000000000000 : ℝ)
    (cell12902 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · norm_num [cell12902]
  · have h := gap_lower (n := 12902) (a := (3309181634631 / 4000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445494749151 / 20000000000000 : ℝ))
      (E := (cell12902 ⟨39, by decide⟩).energy) (xi := (328723415452673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12902 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12902]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12902])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12902) (a := (3309181634631 / 4000000000000 : ℝ)) (b := (31923962883 / 20000000000000 : ℝ)) (q := (445494749151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12902])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12902]

theorem cert12903_20 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41689715516157 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227280968499 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨20, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41689715516157 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227280968499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_21 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83345010402079 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113642486849 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨21, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83345010402079 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113642486849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_22 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41655306962147 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556822246741 / 25000000000000 : ℝ))
      (E := (cell12903 ⟨22, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41655306962147 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556822246741 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_23 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (66620993253 / 80000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227292953371 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨23, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (66620993253 / 80000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227292953371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_24 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83241893295407 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556824248209 / 25000000000000 : ℝ))
      (E := (cell12903 ⟨24, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83241893295407 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556824248209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_25 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83207569079391 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227300991571 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨25, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83207569079391 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227300991571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_26 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41586634442997 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113652505341 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨26, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41586634442997 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113652505341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_27 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (83138992683173 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556827248553 / 25000000000000 : ℝ))
      (E := (cell12903 ⟨27, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (83138992683173 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (556827248553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_28 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (10388092554881 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (44546260057 / 2000000000000 : ℝ))
      (E := (cell12903 ⟨28, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (10388092554881 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (44546260057 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_29 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (5191907007619 / 6250000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113658519319 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨29, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (5191907007619 / 6250000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113658519319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_30 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (10379538462523 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (111366052243 / 5000000000000 : ℝ))
      (E := (cell12903 ⟨30, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (10379538462523 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (111366052243 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_31 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (2593816473203 / 3125000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (222732502303 / 10000000000000 : ℝ))
      (E := (cell12903 ⟨31, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (2593816473203 / 3125000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (222732502303 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_32 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (20741992604401 / 25000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278416129127 / 12500000000000 : ℝ))
      (E := (cell12903 ⟨32, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (20741992604401 / 25000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278416129127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_33 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41466918747217 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (445466603469 / 20000000000000 : ℝ))
      (E := (cell12903 ⟨33, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41466918747217 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (445466603469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_34 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82899728342067 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113668517739 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨34, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82899728342067 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113668517739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_35 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (82865642929743 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227341029447 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨35, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (82865642929743 / 100000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227341029447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_36 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (10353947653357 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278418132289 / 12500000000000 : ℝ))
      (E := (cell12903 ⟨36, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (10353947653357 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278418132289 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_37 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (41398771601479 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278418632951 / 12500000000000 : ℝ))
      (E := (cell12903 ⟨37, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (41398771601479 / 50000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (278418632951 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_38 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (10345441103469 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227353045277 / 100000000000000 : ℝ))
      (E := (cell12903 ⟨38, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (10345441103469 / 12500000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (2227353045277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12903_39 : CellCertificate 12903 (440552525100051 / 5000000000000000 : ℝ) (406965822906657 / 250000000000000000 : ℝ) (328697337396929 / 10000000000000000 : ℝ)
    (cell12903 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · norm_num [cell12903]
  · have h := gap_lower (n := 12903) (a := (16545907614219 / 20000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113678530891 / 50000000000000 : ℝ))
      (E := (cell12903 ⟨39, by decide⟩).energy) (xi := (328697337396929 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12903 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12903]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12903])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12903) (a := (16545907614219 / 20000000000000 : ℝ)) (b := (31921459523 / 20000000000000 : ℝ)) (q := (1113678530891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12903])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12903]

theorem cert12904_20 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20844855635107 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227164333657 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨20, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20844855635107 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227164333657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_21 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (41672501106927 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556792082467 / 25000000000000 : ℝ))
      (E := (cell12904 ⟨21, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (41672501106927 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556792082467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_22 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83310606039307 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445434466969 / 20000000000000 : ℝ))
      (E := (cell12904 ⟨22, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83310606039307 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (445434466969 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_23 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83276233984079 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227176352027 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨23, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83276233984079 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227176352027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_24 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83241886015631 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227180326229 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨24, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83241886015631 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227180326229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_25 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83207562101589 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556796079691 / 25000000000000 : ℝ))
      (E := (cell12904 ⟨25, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83207562101589 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556796079691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_26 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83173262209747 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (222718833237 / 10000000000000 : ℝ))
      (E := (cell12904 ⟨26, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83173262209747 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (222718833237 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_27 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (83138986308063 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227192369549 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨27, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (83138986308063 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227192369549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_28 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (41552367182329 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556799093523 / 25000000000000 : ℝ))
      (E := (cell12904 ⟨28, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (41552367182329 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (556799093523 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_29 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (16614101269563 / 20000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (222720034797 / 10000000000000 : ℝ))
      (E := (cell12904 ⟨29, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (16614101269563 / 20000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (222720034797 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_30 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (41518151112991 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113602175729 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨30, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (41518151112991 / 50000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113602175729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_31 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20750530491941 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227208386141 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨31, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20750530491941 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227208386141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_32 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (10370995692741 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227212394797 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨32, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (10370995692741 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227212394797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_33 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (414669164587 / 500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113608189243 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨33, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (414669164587 / 500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113608189243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_34 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82899724063263 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227220396667 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨34, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82899724063263 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227220396667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_35 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20716409737189 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227224391373 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨35, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20716409737189 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227224391373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_36 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (20707894385819 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (111361421083 / 5000000000000 : ℝ))
      (E := (cell12904 ⟨36, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (20707894385819 / 25000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (111361421083 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_37 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82797539816373 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113616214533 / 50000000000000 : ℝ))
      (E := (cell12904 ⟨37, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82797539816373 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (1113616214533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_38 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (10345440717219 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227236413531 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨38, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (10345440717219 / 12500000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227236413531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12904_39 : CellCertificate 12904 (220269488185497 / 2500000000000000 : ℝ) (813868549484309 / 500000000000000000 : ℝ) (8216781588011 / 250000000000000 : ℝ)
    (cell12904 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · norm_num [cell12904]
  · have h := gap_lower (n := 12904) (a := (82729535277271 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227240433517 / 100000000000000 : ℝ))
      (E := (cell12904 ⟨39, by decide⟩).energy) (xi := (8216781588011 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12904 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12904]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12904])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12904) (a := (82729535277271 / 100000000000000 : ℝ)) (b := (159594782789 / 100000000000000 : ℝ)) (q := (2227240433517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12904])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12904]

theorem cert12905_20 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83379414050079 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445409539017 / 20000000000000 : ℝ))
      (E := (cell12905 ⟨20, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83379414050079 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445409539017 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_21 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83344994027129 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113525841173 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨21, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83344994027129 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113525841173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_22 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (10413824769473 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445411147483 / 20000000000000 : ℝ))
      (E := (cell12905 ⟨22, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (10413824769473 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (445411147483 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_23 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (10409528300417 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113529873533 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨23, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (10409528300417 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113529873533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_24 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41620939368623 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (17398935269 / 781250000000 : ℝ))
      (E := (cell12905 ⟨24, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41620939368623 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (17398935269 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_25 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (10400944390643 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113533879621 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨25, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (10400944390643 / 12500000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113533879621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_26 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83173255534821 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227071708987 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨26, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83173255534821 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227071708987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_27 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41569489967119 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278384467677 / 12500000000000 : ℝ))
      (E := (cell12905 ⟨27, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41569489967119 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (278384467677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_28 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (16620945658303 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227079741901 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨28, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (16620945658303 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227079741901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_29 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83070500574939 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113541885461 / 50000000000000 : ℝ))
      (E := (cell12905 ⟨29, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83070500574939 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (1113541885461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_30 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (20759074188239 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227087771759 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨30, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (20759074188239 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227087771759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_31 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (83002116794173 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227091745927 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨31, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (83002116794173 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227091745927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_32 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41483980333679 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (222709575329 / 10000000000000 : ℝ))
      (E := (cell12905 ⟨32, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41483980333679 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (222709575329 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_33 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82933828341437 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227099794977 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨33, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82933828341437 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227099794977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_34 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (82899719785493 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556775953317 / 25000000000000 : ℝ))
      (E := (cell12905 ⟨34, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (82899719785493 / 100000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556775953317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_35 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (1294775546387 / 1562500000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (222710780877 / 10000000000000 : ℝ))
      (E := (cell12905 ⟨35, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (1294775546387 / 1562500000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (222710780877 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_36 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (41415786930329 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556777945467 / 25000000000000 : ℝ))
      (E := (cell12905 ⟨36, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (41415786930329 / 50000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556777945467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_37 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (16559507286143 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (111355789571 / 5000000000000 : ℝ))
      (E := (cell12905 ⟨37, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (16559507286143 / 20000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (111355789571 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_38 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (20690880662161 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556779959359 / 25000000000000 : ℝ))
      (E := (cell12905 ⟨38, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (20690880662161 / 25000000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (556779959359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12905_39 : CellCertificate 12905 (881050859309769 / 10000000000000000 : ℝ) (406902731468527 / 250000000000000000 : ℝ) (328645193822133 / 10000000000000000 : ℝ)
    (cell12905 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · norm_num [cell12905]
  · have h := gap_lower (n := 12905) (a := (5170595780269 / 6250000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227123802219 / 100000000000000 : ℝ))
      (E := (cell12905 ⟨39, by decide⟩).energy) (xi := (328645193822133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12905 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12905]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12905])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12905) (a := (5170595780269 / 6250000000000 : ℝ)) (b := (31916453987 / 20000000000000 : ℝ)) (q := (2227123802219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12905])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12905]

theorem cert12906_20 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83379405561267 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226931111081 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨20, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83379405561267 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226931111081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_21 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (16668997168381 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113467573887 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨21, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (16668997168381 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113467573887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_22 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (3332423610949 / 4000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (222693913633 / 10000000000000 : ℝ))
      (E := (cell12906 ⟨22, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (3332423610949 / 4000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (222693913633 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_23 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83276218824021 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113471569243 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨23, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83276218824021 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113471569243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_24 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41620935730127 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445389431489 / 20000000000000 : ℝ))
      (E := (cell12906 ⟨24, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41620935730127 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445389431489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_25 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41603774075027 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (13918444611 / 625000000000 : ℝ))
      (E := (cell12906 ⟨25, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41603774075027 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (13918444611 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_26 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (16634649772243 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (278369392567 / 12500000000000 : ℝ))
      (E := (cell12906 ⟨26, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (16634649772243 / 20000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (278369392567 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_27 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (2598092923803 / 3125000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113479584137 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨27, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (2598092923803 / 3125000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113479584137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_28 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83104722219621 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226963164761 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨28, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83104722219621 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226963164761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_29 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (3322819792131 / 4000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226967190477 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨29, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (3322819792131 / 4000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226967190477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_30 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41518145640553 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226971188701 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨30, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41518145640553 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226971188701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_31 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (83002111621723 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445395032189 / 20000000000000 : ℝ))
      (E := (cell12906 ⟨31, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (83002111621723 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (445395032189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_32 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (20741988948473 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (89079166683 / 4000000000000 : ℝ))
      (E := (cell12906 ⟨32, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (20741988948473 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (89079166683 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_33 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41466911883271 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226983208219 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨33, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41466911883271 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2226983208219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_34 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82899715508757 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (556746792007 / 25000000000000 : ℝ))
      (E := (cell12906 ⟨34, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82899715508757 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (556746792007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_35 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41432815494889 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (556747805747 / 25000000000000 : ℝ))
      (E := (cell12906 ⟨35, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41432815494889 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (556747805747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_36 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (82831570179003 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113497598803 / 50000000000000 : ℝ))
      (E := (cell12906 ⟨36, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (82831570179003 / 100000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (1113497598803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_37 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (2587422907687 / 3125000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (556749802341 / 25000000000000 : ℝ))
      (E := (cell12906 ⟨37, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (2587422907687 / 3125000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (556749802341 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_38 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (20690879890107 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (34796924993 / 1562500000000 : ℝ))
      (E := (cell12906 ⟨38, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (20690879890107 / 25000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (34796924993 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12906_39 : CellCertificate 12906 (176204753980501 / 2000000000000000 : ℝ) (406871193084637 / 250000000000000000 : ℝ) (328619128300931 / 10000000000000000 : ℝ)
    (cell12906 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · norm_num [cell12906]
  · have h := gap_lower (n := 12906) (a := (41364764846097 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227007226631 / 100000000000000 : ℝ))
      (E := (cell12906 ⟨39, by decide⟩).energy) (xi := (328619128300931 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12906 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12906]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12906])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12906) (a := (41364764846097 / 50000000000000 : ℝ)) (b := (159569759053 / 100000000000000 : ℝ)) (q := (2227007226631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12906])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12906]

theorem cert12907_20 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83379397073991 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226814523349 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨20, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83379397073991 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226814523349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_21 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83344977658181 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226818551189 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨21, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83344977658181 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226818551189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_22 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (8331058239313 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445364517987 / 20000000000000 : ℝ))
      (E := (cell12907 ⟨22, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (8331058239313 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445364517987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_23 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83276211246133 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226826584657 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨23, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83276211246133 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226826584657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_24 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83241864184653 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113415298439 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨24, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83241864184653 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113415298439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_25 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83207541176319 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226834571151 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨25, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83207541176319 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226834571151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_26 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (649790954601 / 781250000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113419284289 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨26, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (649790954601 / 781250000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113419284289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_27 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41569483595219 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113421295831 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨27, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41569483595219 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113421295831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_28 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41552358074487 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556711646047 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨28, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41552358074487 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556711646047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_29 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83070489032823 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445370121327 / 20000000000000 : ℝ))
      (E := (cell12907 ⟨29, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83070489032823 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (445370121327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_30 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (83036285810433 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226854602281 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨30, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (83036285810433 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226854602281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_31 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (20750526612603 / 25000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556714657799 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨31, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (20750526612603 / 25000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556714657799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_32 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82967950921531 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (278357829519 / 12500000000000 : ℝ))
      (E := (cell12907 ⟨32, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82967950921531 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (278357829519 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_33 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82933819192717 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226866618209 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨33, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82933819192717 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226866618209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_34 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41449855616527 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113435318413 / 50000000000000 : ℝ))
      (E := (cell12907 ⟨34, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41449855616527 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (1113435318413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_35 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (41432813505893 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226874634029 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨35, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (41432813505893 / 50000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226874634029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_36 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (8283156649831 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556719667219 / 25000000000000 : ℝ))
      (E := (cell12907 ⟨36, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (8283156649831 / 10000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (556719667219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_37 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (82797529662181 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226882624203 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨37, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (82797529662181 / 100000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226882624203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_38 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (5172719779569 / 6250000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226886676039 / 100000000000000 : ℝ))
      (E := (cell12907 ⟨38, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (5172719779569 / 6250000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (2226886676039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12907_39 : CellCertificate 12907 (110124585564907 / 1250000000000000 : ℝ) (1627358638357391 / 1000000000000000000 : ℝ) (164296533477881 / 5000000000000000 : ℝ)
    (cell12907 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · norm_num [cell12907]
  · have h := gap_lower (n := 12907) (a := (4136476345047 / 5000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (222689064801 / 10000000000000 : ℝ))
      (E := (cell12907 ⟨39, by decide⟩).energy) (xi := (164296533477881 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12907 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12907]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12907])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12907) (a := (4136476345047 / 5000000000000 : ℝ)) (b := (159557250143 / 100000000000000 : ℝ)) (q := (222689064801 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12907])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12907]

theorem cert12908_20 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83379388588251 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226697990187 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨20, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83379388588251 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226697990187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_21 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (20836242368989 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (445340401847 / 20000000000000 : ℝ))
      (E := (cell12908 ⟨21, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (20836242368989 / 25000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (445340401847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_22 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83310574513999 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113353019943 / 50000000000000 : ℝ))
      (E := (cell12908 ⟨22, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83310574513999 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113353019943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_23 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83276203669673 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226710027211 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨23, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83276203669673 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226710027211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_24 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83241856910443 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226714032731 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨24, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83241856910443 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226714032731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_25 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (4160376710197 / 5000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226718059413 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨25, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (4160376710197 / 5000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226718059413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_26 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (2079330887949 / 2500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226722051553 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨26, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (2079330887949 / 2500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226722051553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_27 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (83138960820463 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226726070043 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨27, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (83138960820463 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226726070043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_28 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41552355039787 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226730058669 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨28, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41552355039787 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226730058669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_29 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41535241631791 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226734077907 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨29, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41535241631791 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226734077907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_30 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (16607256068187 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (445347614207 / 20000000000000 : ℝ))
      (E := (cell12908 ⟨30, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (16607256068187 / 20000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (445347614207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_31 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41501050640121 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226742098123 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨31, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41501050640121 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226742098123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_32 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41483973025137 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (278343262743 / 12500000000000 : ℝ))
      (E := (cell12908 ⟨32, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41483973025137 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (278343262743 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_33 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (2073345365499 / 2500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226750083553 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨33, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (2073345365499 / 2500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226750083553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_34 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (5181231684899 / 6250000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226754102411 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨34, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (5181231684899 / 6250000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226754102411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_35 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82865623034791 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226758100543 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨35, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82865623034791 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226758100543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_36 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (4141578140929 / 5000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556690519583 / 25000000000000 : ℝ))
      (E := (cell12908 ⟨36, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (4141578140929 / 5000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (556690519583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_37 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (10349690784913 / 12500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113383047317 / 50000000000000 : ℝ))
      (E := (cell12908 ⟨37, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (10349690784913 / 12500000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (1113383047317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_38 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (82763513386671 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226770149457 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨38, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (82763513386671 / 100000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226770149457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12908_39 : CellCertificate 12908 (22024240078977 / 250000000000000 : ℝ) (162723252392609 / 100000000000000000 : ℝ) (20535438111597 / 625000000000000 : ℝ)
    (cell12908 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · norm_num [cell12908]
  · have h := gap_lower (n := 12908) (a := (41364762055271 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226774125101 / 100000000000000 : ℝ))
      (E := (cell12908 ⟨39, by decide⟩).energy) (xi := (20535438111597 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12908 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12908]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12908])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12908) (a := (41364762055271 / 50000000000000 : ℝ)) (b := (31908948641 / 20000000000000 : ℝ)) (q := (2226774125101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12908])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12908]

theorem cert12909_20 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41689690052023 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226581511597 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨20, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41689690052023 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226581511597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_21 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83344961295231 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226585521913 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨21, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83344961295231 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226585521913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_22 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (8331056663633 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (445317897237 / 20000000000000 : ℝ))
      (E := (cell12909 ⟨22, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (8331056663633 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (445317897237 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_23 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83276196094639 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226593524519 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨23, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83276196094639 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226593524519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_24 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (10405231204703 / 12500000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113298761699 / 50000000000000 : ℝ))
      (E := (cell12909 ⟨24, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (10405231204703 / 12500000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (1113298761699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_25 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (16641505446583 / 20000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (445320308827 / 20000000000000 : ℝ))
      (E := (cell12909 ⟨25, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (16641505446583 / 20000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (445320308827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_26 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (8317322884831 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (139162845689 / 6250000000000 : ℝ))
      (E := (cell12909 ⟨26, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (8317322884831 / 10000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (139162845689 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_27 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83138954451771 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556652386239 / 25000000000000 : ℝ))
      (E := (cell12909 ⟨27, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83138954451771 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556652386239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_28 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41552352005711 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226613529717 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨28, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41552352005711 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226613529717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_29 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (324494052717 / 390625000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (278327193223 / 12500000000000 : ℝ))
      (E := (cell12909 ⟨29, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (324494052717 / 390625000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (278327193223 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_30 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (20759068718153 / 25000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226621536433 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨30, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (20759068718153 / 25000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226621536433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_31 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (83002096111211 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226625561731 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨31, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (83002096111211 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226625561731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_32 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82967941180121 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226629564451 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨32, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82967941180121 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226629564451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_33 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82933810048271 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556658401063 / 25000000000000 : ℝ))
      (E := (cell12909 ⟨33, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82933810048271 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556658401063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_34 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82899702684747 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (445327512957 / 20000000000000 : ℝ))
      (E := (cell12909 ⟨34, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82899702684747 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (445327512957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_35 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (41432809529397 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226641563881 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨35, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (41432809529397 / 50000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226641563881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_36 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82831559139811 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556661400499 / 25000000000000 : ℝ))
      (E := (cell12909 ⟨36, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82831559139811 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (556661400499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_37 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82797522897353 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (111332481033 / 5000000000000 : ℝ))
      (E := (cell12909 ⟨37, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82797522897353 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (111332481033 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_38 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82763510301129 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (222665361981 / 10000000000000 : ℝ))
      (E := (cell12909 ⟨38, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82763510301129 / 100000000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (222665361981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12909_39 : CellCertificate 12909 (880942525821039 / 10000000000000000 : ℝ) (1627106429040101 / 1000000000000000000 : ℝ) (164270478394613 / 5000000000000000 : ℝ)
    (cell12909 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · norm_num [cell12909]
  · have h := gap_lower (n := 12909) (a := (82729521321 / 100000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226657599161 / 100000000000000 : ℝ))
      (E := (cell12909 ⟨39, by decide⟩).energy) (xi := (164270478394613 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12909 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12909]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12909])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12909) (a := (82729521321 / 100000000000 : ℝ)) (b := (159532238237 / 100000000000000 : ℝ)) (q := (2226657599161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12909])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12909]

theorem cert12910_20 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83379371621377 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (13915406433 / 625000000000 : ℝ))
      (E := (cell12910 ⟨20, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83379371621377 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (13915406433 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_21 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20836238279001 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113234515451 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨21, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20836238279001 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113234515451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_22 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20827639690031 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226473045523 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨22, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20827639690031 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226473045523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_23 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83276188521033 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (222647701821 / 10000000000000 : ℝ))
      (E := (cell12910 ⟨23, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83276188521033 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (222647701821 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_24 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20810460591549 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113240505243 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨24, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20810460591549 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113240505243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_25 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (16641504052649 / 20000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445297005063 / 20000000000000 : ℝ))
      (E := (cell12910 ⟨25, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (16641504052649 / 20000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445297005063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_26 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83173222179979 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226489065429 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨26, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83173222179979 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226489065429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_27 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83138948084361 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445298614973 / 20000000000000 : ℝ))
      (E := (cell12910 ⟨27, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83138948084361 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445298614973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_28 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20776174486129 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113248527911 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨28, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20776174486129 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113248527911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_29 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (83070471728733 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226501068777 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨29, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (83070471728733 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226501068777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_30 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (10379533675683 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445301011401 / 20000000000000 : ℝ))
      (E := (cell12910 ⟨30, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (10379533675683 / 12500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445301011401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_31 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (2075052273583 / 2500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556627270143 / 25000000000000 : ℝ))
      (E := (cell12910 ⟨31, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (2075052273583 / 2500000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556627270143 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_32 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (2592748009721 / 3125000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556628270563 / 25000000000000 : ℝ))
      (E := (cell12910 ⟨32, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (2592748009721 / 3125000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556628270563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_33 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (1658676109553 / 2000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226517063101 / 100000000000000 : ℝ))
      (E := (cell12910 ⟨33, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (1658676109553 / 2000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (2226517063101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_34 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82899698412143 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556630270643 / 25000000000000 : ℝ))
      (E := (cell12910 ⟨34, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82899698412143 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (556630270643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_35 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41432807541897 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113262541347 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨35, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41432807541897 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113262541347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_36 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (20707888865501 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (55663228063 / 2500000000000 : ℝ))
      (E := (cell12910 ⟨36, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (20707888865501 / 25000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (55663228063 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_37 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (82797519516329 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113266571791 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨37, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (82797519516329 / 100000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113266571791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_38 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41381753608239 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445307429163 / 20000000000000 : ℝ))
      (E := (cell12910 ⟨38, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41381753608239 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (445307429163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12910_39 : CellCertificate 12910 (880915452504193 / 10000000000000000 : ℝ) (10168627210593 / 6250000000000000 : ℝ) (164257453982857 / 5000000000000000 : ℝ)
    (cell12910 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · norm_num [cell12910]
  · have h := gap_lower (n := 12910) (a := (41364759266157 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113270564467 / 50000000000000 : ℝ))
      (E := (cell12910 ⟨39, by decide⟩).energy) (xi := (164257453982857 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12910 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12910]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12910])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12910) (a := (41364759266157 / 50000000000000 : ℝ)) (b := (3987993381 / 2500000000000 : ℝ)) (q := (1113270564467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12910])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12910]

theorem cert12911_20 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41689681570121 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (55658713581 / 2500000000000 : ℝ))
      (E := (cell12911 ⟨20, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41689681570121 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (55658713581 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_21 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (20836236234569 / 25000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556588134051 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨21, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (20836236234569 / 25000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556588134051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_22 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (4165527544269 / 5000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113178271433 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨22, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (4165527544269 / 5000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113178271433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_23 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (20819045237213 / 25000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226360566659 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨23, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (20819045237213 / 25000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226360566659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_24 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83241835096157 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226364552391 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨24, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83241835096157 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226364552391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_25 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83207513294929 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556592140343 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨25, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83207513294929 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556592140343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_26 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83173215512967 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226372596331 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨26, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83173215512967 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226372596331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_27 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83138941718233 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556594150327 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨27, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83138941718233 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556594150327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_28 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (10388086484857 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113190289249 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨28, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (10388086484857 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113190289249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_29 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (132912745541 / 160000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226384588377 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨29, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (132912745541 / 160000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226384588377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_30 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (83036263939491 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113194316377 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨30, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (83036263939491 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113194316377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_31 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (10375260722071 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445278519219 / 20000000000000 : ℝ))
      (E := (cell12911 ⟨31, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (10375260722071 / 12500000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (445278519219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_32 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41483965721563 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556599149193 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨32, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41483965721563 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556599149193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_33 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41466900454049 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556600158977 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨33, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41466900454049 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556600158977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_34 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (8289969414057 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113202327889 / 50000000000000 : ℝ))
      (E := (cell12911 ⟨34, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (8289969414057 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (1113202327889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_35 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (8286561110979 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278301082123 / 12500000000000 : ℝ))
      (E := (cell12911 ⟨35, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (8286561110979 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (278301082123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_36 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41415775892579 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556603159977 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨36, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41415775892579 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556603159977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_37 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (8279751613623 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556604165851 / 25000000000000 : ℝ))
      (E := (cell12911 ⟨37, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (8279751613623 / 10000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (556604165851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_38 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (82763504132717 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226420668757 / 100000000000000 : ℝ))
      (E := (cell12911 ⟨38, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (82763504132717 / 100000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (2226420668757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12911_39 : CellCertificate 12911 (440444191603801 / 5000000000000000 : ℝ) (325370859577177 / 200000000000000000 : ℝ) (328488863313941 / 10000000000000000 : ℝ)
    (cell12911 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · norm_num [cell12911]
  · have h := gap_lower (n := 12911) (a := (41364757872241 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (6957577049 / 312500000000 : ℝ))
      (E := (cell12911 ⟨39, by decide⟩).energy) (xi := (328488863313941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12911 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12911]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12911])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12911) (a := (41364757872241 / 50000000000000 : ℝ)) (b := (39876808553 / 25000000000000 : ℝ)) (q := (6957577049 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12911])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12911]

theorem cert12912_20 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83379354660641 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113116055887 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨20, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83379354660641 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113116055887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_21 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41672468381023 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226236154463 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨21, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41672468381023 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226236154463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_22 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41655271506049 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226240153249 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨22, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41655271506049 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226240153249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_23 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83276173378097 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113122055747 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨23, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83276173378097 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113122055747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_24 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (20810456956877 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (278281018639 / 12500000000000 : ℝ))
      (E := (cell12912 ⟨24, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (20810456956877 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (278281018639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_25 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83207506327967 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (139140759519 / 6250000000000 : ℝ))
      (E := (cell12912 ⟨25, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83207506327967 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (139140759519 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_26 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (10396651105909 / 12500000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226256182171 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨26, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (10396651105909 / 12500000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226256182171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_27 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83138935353387 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556565045687 / 25000000000000 : ℝ))
      (E := (cell12912 ⟨27, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83138935353387 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556565045687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_28 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41552342907221 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (222626415623 / 10000000000000 : ℝ))
      (E := (cell12912 ⟨28, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41552342907221 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (222626415623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_29 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41535230099363 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445253632619 / 20000000000000 : ℝ))
      (E := (cell12912 ⟨29, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41535230099363 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (445253632619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_30 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (83036258474693 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226272205147 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨30, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (83036258474693 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226272205147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_31 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41501040305477 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (278284520857 / 12500000000000 : ℝ))
      (E := (cell12912 ⟨31, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41501040305477 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (278284520857 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_32 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (20741981644071 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556570041647 / 25000000000000 : ℝ))
      (E := (cell12912 ⟨32, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (20741981644071 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (556570041647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_33 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (20733449084903 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (222628420547 / 10000000000000 : ℝ))
      (E := (cell12912 ⟨33, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (20733449084903 / 25000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (222628420547 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_34 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (8289968987003 / 10000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226288225773 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨34, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (8289968987003 / 10000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226288225773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_35 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82865607136783 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226292228101 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨35, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82865607136783 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226292228101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_36 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82831548109273 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (69571756651 / 3125000000000 : ℝ))
      (E := (cell12912 ⟨36, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82831548109273 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (69571756651 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_37 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82797512757057 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113150119411 / 50000000000000 : ℝ))
      (E := (cell12912 ⟨37, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82797512757057 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (1113150119411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_38 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (82763501049847 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226304247353 / 100000000000000 : ℝ))
      (E := (cell12912 ⟨38, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (82763501049847 / 100000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (2226304247353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12912_39 : CellCertificate 12912 (110107664741291 / 1250000000000000 : ℝ) (12708814543817 / 7812500000000000 : ℝ) (328462822832837 / 10000000000000000 : ℝ)
    (cell12912 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · norm_num [cell12912]
  · have h := gap_lower (n := 12912) (a := (41364756478753 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (111315411907 / 5000000000000 : ℝ))
      (E := (cell12912 ⟨39, by decide⟩).energy) (xi := (328462822832837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12912 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12912]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12912])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12912) (a := (41364756478753 / 50000000000000 : ℝ)) (b := (79747367577 / 50000000000000 : ℝ)) (q := (111315411907 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12912])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12912]

theorem cert12913_20 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41689673091287 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445223146977 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨20, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41689673091287 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445223146977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_21 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41672464293657 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445223942143 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨21, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41672464293657 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445223942143 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_22 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41655267570139 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113061850819 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨22, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41655267570139 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113061850819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_23 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83276165808767 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (139132981943 / 6250000000000 : ℝ))
      (E := (cell12913 ⟨23, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83276165808767 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (139132981943 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_24 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83241820560249 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226131742259 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨24, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83241820560249 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226131742259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_25 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83207499362357 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226135739701 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨25, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83207499362357 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226135739701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_26 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41586601091447 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226139764511 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨26, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41586601091447 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226139764511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_27 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83138928989823 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556535940181 / 25000000000000 : ℝ))
      (E := (cell12913 ⟨27, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83138928989823 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556535940181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_28 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41552339875637 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (278268466317 / 12500000000000 : ℝ))
      (E := (cell12913 ⟨28, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41552339875637 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (278268466317 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_29 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41535227217769 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226151734421 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨29, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41535227217769 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226151734421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_30 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (20759063252767 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556538943547 / 25000000000000 : ℝ))
      (E := (cell12913 ⟨30, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (20759063252767 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556538943547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_31 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (83002075446479 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445231958571 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨31, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (83002075446479 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445231958571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_32 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82967921710543 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (278270473963 / 12500000000000 : ℝ))
      (E := (cell12913 ⟨32, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82967921710543 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (278270473963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_33 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (41466895886097 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556541942947 / 25000000000000 : ℝ))
      (E := (cell12913 ⟨33, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (41466895886097 / 50000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (556541942947 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_34 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82899685600521 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226171792561 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨34, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82899685600521 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226171792561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_35 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (20716400791193 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445235159209 / 20000000000000 : ℝ))
      (E := (cell12913 ⟨35, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (20716400791193 / 25000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (445235159209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_36 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82831544434349 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226179782621 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨36, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82831544434349 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226179782621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_37 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (8279750937881 / 10000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226183811141 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨37, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (8279750937881 / 10000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226183811141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_38 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (82763497967867 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226187822887 / 100000000000000 : ℝ))
      (E := (cell12913 ⟨38, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (82763497967867 / 100000000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (2226187822887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12913_39 : CellCertificate 12913 (110104282083929 / 1250000000000000 : ℝ) (813301122429207 / 500000000000000000 : ℝ) (32843678652133 / 1000000000000000 : ℝ)
    (cell12913 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · norm_num [cell12913]
  · have h := gap_lower (n := 12913) (a := (10341188771423 / 12500000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113095908787 / 50000000000000 : ℝ))
      (E := (cell12913 ⟨39, by decide⟩).energy) (xi := (32843678652133 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12913 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12913]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12913])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12913) (a := (10341188771423 / 12500000000000 : ℝ)) (b := (9967639879 / 6250000000000 : ℝ)) (q := (1113095908787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12913])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12913]

theorem cert12914_20 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83379337706041 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225999354273 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨20, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83379337706041 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2225999354273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_21 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83344920414079 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226003321603 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨21, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83344920414079 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226003321603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_22 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83310527269919 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226007363071 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨22, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83310527269919 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226007363071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_23 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41638079120431 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226011365439 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨23, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41638079120431 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226011365439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_24 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41620906647189 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (278251916479 / 12500000000000 : ℝ))
      (E := (cell12914 ⟨24, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41620906647189 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (278251916479 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_25 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83207492398101 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (89040775279 / 4000000000000 : ℝ))
      (E := (cell12914 ⟨25, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83207492398101 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (89040775279 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_26 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83173195519833 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226023343349 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨26, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83173195519833 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226023343349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_27 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (4156946131377 / 5000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113013696849 / 50000000000000 : ℝ))
      (E := (cell12914 ⟨27, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (4156946131377 / 5000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113013696849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_28 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83104673689351 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (22260313599 / 1000000000000 : ℝ))
      (E := (cell12914 ⟨28, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83104673689351 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (22260313599 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_29 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (83070448673559 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556508840217 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨29, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (83070448673559 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556508840217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_30 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41518123774309 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113019699203 / 50000000000000 : ℝ))
      (E := (cell12914 ⟨30, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41518123774309 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113019699203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_31 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41501035141571 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226043415537 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨31, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41501035141571 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226043415537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_32 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (41483958422953 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113023706769 / 50000000000000 : ℝ))
      (E := (cell12914 ⟨32, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (41483958422953 / 50000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113023706769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_33 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (82933787205843 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (278256424183 / 12500000000000 : ℝ))
      (E := (cell12914 ⟨33, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (82933787205843 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (278256424183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_34 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (20724920333011 / 25000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226055414767 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨34, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (20724920333011 / 25000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226055414767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_35 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (82865599193757 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556514854867 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨35, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (82865599193757 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556514854867 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_36 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (16566308152077 / 20000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556515851987 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨36, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (16566308152077 / 20000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556515851987 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_37 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (82797506001487 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113033719529 / 50000000000000 : ℝ))
      (E := (cell12914 ⟨37, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (82797506001487 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (1113033719529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_38 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (10345436860847 / 12500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226071454079 / 100000000000000 : ℝ))
      (E := (cell12914 ⟨38, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (10345436860847 / 12500000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (2226071454079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12914_39 : CellCertificate 12914 (110100899928747 / 1250000000000000 : ℝ) (1626476247630861 / 1000000000000000000 : ℝ) (328410754378349 / 10000000000000000 : ℝ)
    (cell12914 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · norm_num [cell12914]
  · have h := gap_lower (n := 12914) (a := (82729507386117 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556518863181 / 25000000000000 : ℝ))
      (E := (cell12914 ⟨39, by decide⟩).energy) (xi := (328410754378349 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12914 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12914]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12914])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12914) (a := (82729507386117 / 100000000000000 : ℝ)) (b := (159469742943 / 100000000000000 : ℝ)) (q := (556518863181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12914])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12914]

theorem cert12915_20 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83379329231041 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225882969939 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨20, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83379329231041 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225882969939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_21 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83344912242341 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222588698713 / 10000000000000 : ℝ))
      (E := (cell12915 ⟨21, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83344912242341 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222588698713 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_22 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83310519401021 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222589096251 / 10000000000000 : ℝ))
      (E := (cell12915 ⟨22, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83310519401021 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222589096251 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_23 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83276150674383 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225895016179 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨23, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83276150674383 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225895016179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_24 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (10405225753737 / 12500000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (69559343007 / 3125000000000 : ℝ))
      (E := (cell12915 ⟨24, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (10405225753737 / 12500000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (69559343007 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_25 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41603742717599 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225903020713 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨25, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41603742717599 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225903020713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_26 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83173188858089 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (278238372141 / 12500000000000 : ℝ))
      (E := (cell12915 ⟨26, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83173188858089 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (278238372141 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_27 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41569458133269 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222591102321 / 10000000000000 : ℝ))
      (E := (cell12915 ⟨27, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41569458133269 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (222591102321 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_28 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83104667628673 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (89036601773 / 4000000000000 : ℝ))
      (E := (cell12915 ⟨28, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83104667628673 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (89036601773 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_29 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83070442912789 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112959521217 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨29, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83070442912789 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112959521217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_30 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83036242087341 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (278240377409 / 12500000000000 : ℝ))
      (E := (cell12915 ⟨30, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83036242087341 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (278240377409 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_31 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (83002065120943 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112963517451 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨31, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (83002065120943 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112963517451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_32 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82967911982371 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225931032093 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨32, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82967911982371 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225931032093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_33 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41466891320279 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225935070501 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨33, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41466891320279 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225935070501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_34 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41449838532299 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445187806753 / 20000000000000 : ℝ))
      (E := (cell12915 ⟨34, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41449838532299 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (445187806753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_35 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (82865595223737 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225943039721 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨35, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (82865595223737 / 100000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225943039721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_36 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (41415768543691 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112973544407 / 50000000000000 : ℝ))
      (E := (cell12915 ⟨36, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (41415768543691 / 50000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (1112973544407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_37 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (8279750262509 / 10000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (17807608511 / 800000000000 : ℝ))
      (E := (cell12915 ⟨37, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (8279750262509 / 10000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (17807608511 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_38 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (3310539672263 / 4000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (69561096319 / 3125000000000 : ℝ))
      (E := (cell12915 ⟨38, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (3310539672263 / 4000000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (69561096319 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12915_39 : CellCertificate 12915 (880780146205021 / 10000000000000000 : ℝ) (81317513496069 / 50000000000000000 : ℝ) (41048090800353 / 1250000000000000 : ℝ)
    (cell12915 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · norm_num [cell12915]
  · have h := gap_lower (n := 12915) (a := (10341188075213 / 12500000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225959084849 / 100000000000000 : ℝ))
      (E := (cell12915 ⟨39, by decide⟩).energy) (xi := (41048090800353 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12915 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12915]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12915])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12915) (a := (10341188075213 / 12500000000000 : ℝ)) (b := (15945724979 / 10000000000000 : ℝ)) (q := (2225959084849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12915])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12915]

theorem cert12916_20 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41689660378787 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112883320093 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨20, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41689660378787 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112883320093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_21 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83344904072099 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (89030825959 / 4000000000000 : ℝ))
      (E := (cell12916 ⟨21, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83344904072099 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (89030825959 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_22 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83310511533583 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225774674997 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨22, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83310511533583 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225774674997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_23 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83276143109327 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (139111166457 / 6250000000000 : ℝ))
      (E := (cell12916 ⟨23, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83276143109327 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (139111166457 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_24 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83241798766803 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556445668859 / 25000000000000 : ℝ))
      (E := (cell12916 ⟨24, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83241798766803 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556445668859 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_25 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41603739236823 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225786655917 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨25, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41603739236823 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225786655917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_26 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41586591098831 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225790665847 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨26, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41586591098831 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225790665847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_27 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (649522733647 / 781250000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556448676931 / 25000000000000 : ℝ))
      (E := (cell12916 ⟨27, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (649522733647 / 781250000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556448676931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_28 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (2077616539231 / 2500000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225798666839 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨28, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (2077616539231 / 2500000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225798666839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_29 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83070437153229 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556450680153 / 25000000000000 : ℝ))
      (E := (cell12916 ⟨29, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83070437153229 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556450680153 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_30 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83036236627237 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (55645167383 / 2500000000000 : ℝ))
      (E := (cell12916 ⟨30, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83036236627237 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (55645167383 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_31 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (83002059959881 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (222581070951 / 10000000000000 : ℝ))
      (E := (cell12916 ⟨31, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (83002059959881 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (222581070951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_32 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (82967907119937 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (44516294119 / 2000000000000 : ℝ))
      (E := (cell12916 ⟨32, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (82967907119937 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (44516294119 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_33 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (4146688903817 / 5000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445163748859 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨33, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (4146688903817 / 5000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445163748859 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_34 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41449836399091 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112911354093 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨34, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41449836399091 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112911354093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_35 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (82865591254713 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445165343091 / 20000000000000 : ℝ))
      (E := (cell12916 ⟨35, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (82865591254713 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (445165343091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_36 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41415766707669 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112915353937 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨36, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41415766707669 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112915353937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_37 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (82797499249617 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112917372147 / 50000000000000 : ℝ))
      (E := (cell12916 ⟨37, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (82797499249617 / 100000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (1112917372147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_38 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (2586359022727 / 3125000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225838765997 / 100000000000000 : ℝ))
      (E := (cell12916 ⟨38, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (2586359022727 / 3125000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (2225838765997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12916_39 : CellCertificate 12916 (880753096995631 / 10000000000000000 : ℝ) (1626224311725437 / 1000000000000000000 : ℝ) (65671740518737 / 2000000000000000 : ℝ)
    (cell12916 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · norm_num [cell12916]
  · have h := gap_lower (n := 12916) (a := (41364750909073 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556460693173 / 25000000000000 : ℝ))
      (E := (cell12916 ⟨39, by decide⟩).energy) (xi := (65671740518737 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12916 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12916]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12916])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12916) (a := (41364750909073 / 50000000000000 : ℝ)) (b := (39861189651 / 25000000000000 : ℝ)) (q := (556460693173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12916])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12916]

theorem cert12917_20 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83379312285639 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225650365011 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨20, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83379312285639 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225650365011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_21 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41672447951677 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225654365459 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨21, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41672447951677 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225654365459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_22 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (16662100733521 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225658325491 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨22, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (16662100733521 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225658325491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_23 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (16655227109139 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445132473041 / 20000000000000 : ℝ))
      (E := (cell12917 ⟨23, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (16655227109139 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (445132473041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_24 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83241791505097 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112833185539 / 50000000000000 : ℝ))
      (E := (cell12917 ⟨24, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83241791505097 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (1112833185539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_25 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83207471513447 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225670346001 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨25, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83207471513447 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225670346001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_26 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (1663463510771 / 2000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225674351069 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨26, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (1663463510771 / 2000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225674351069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_27 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41569451774187 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225678388777 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨27, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41569451774187 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225678388777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_28 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (83104655511051 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225682402901 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨28, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (83104655511051 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225682402901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_29 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (20767607848719 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225686395403 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨29, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (20767607848719 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225686395403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_30 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41518115584153 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139105648001 / 6250000000000 : ℝ))
      (E := (cell12917 ⟨30, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41518115584153 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139105648001 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_31 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (20750513699989 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225694380803 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨31, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (20750513699989 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225694380803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_32 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (16593580451721 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139106148533 / 6250000000000 : ℝ))
      (E := (cell12917 ⟨32, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (16593580451721 / 20000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139106148533 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_33 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (20733443378297 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225702414847 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨33, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (20733443378297 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225702414847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_34 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82899668532797 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (556426609507 / 25000000000000 : ℝ))
      (E := (cell12917 ⟨34, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82899668532797 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (556426609507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_35 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (20716396821671 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225710446669 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨35, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (20716396821671 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225710446669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_36 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (41415764872127 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225714441147 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨36, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (41415764872127 / 50000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225714441147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_37 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (20699373968767 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139107401351 / 6250000000000 : ℝ))
      (E := (cell12917 ⟨37, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (20699373968767 / 25000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (139107401351 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_38 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82763485648841 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (89028897869 / 4000000000000 : ℝ))
      (E := (cell12917 ⟨38, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82763485648841 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (89028897869 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12917_39 : CellCertificate 12917 (880726051800867 / 10000000000000000 : ℝ) (813049186519249 / 500000000000000000 : ℝ) (328332682949861 / 10000000000000000 : ℝ)
    (cell12917 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · norm_num [cell12917]
  · have h := gap_lower (n := 12917) (a := (82729499035441 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225726457511 / 100000000000000 : ℝ))
      (E := (cell12917 ⟨39, by decide⟩).energy) (xi := (328332682949861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12917 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12917]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12917])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12917) (a := (82729499035441 / 100000000000000 : ℝ)) (b := (79716134693 / 50000000000000 : ℝ)) (q := (2225726457511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12917])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12917]

theorem cert12918_20 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (83379303815237 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (111276701391 / 5000000000000 : ℝ))
      (E := (cell12918 ⟨20, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (83379303815237 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (111276701391 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_21 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (16668977547221 / 20000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225538078263 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨21, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (16668977547221 / 20000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225538078263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_22 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (83310495803087 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112771044517 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨22, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (83310495803087 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112771044517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_23 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (83276127983487 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556386515873 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨23, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (83276127983487 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556386515873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_24 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (83241784244779 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (44511001263 / 2000000000000 : ℝ))
      (E := (cell12918 ⟨24, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (83241784244779 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (44511001263 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_25 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (416037322773 / 500000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225554090969 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨25, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (416037322773 / 500000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225554090969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_26 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41586584440377 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445111618247 / 20000000000000 : ℝ))
      (E := (cell12918 ⟨26, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41586584440377 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (445111618247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_27 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20784724297803 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225562066371 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨27, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20784724297803 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225562066371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_28 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41552324727053 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112783038527 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨28, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41552324727053 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112783038527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_29 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20767606409433 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112785062659 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨29, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20767606409433 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112785062659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_30 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (83036225710547 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225574095897 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨30, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (83036225710547 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225574095897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_31 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (5187628102573 / 6250000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (111278905367 / 5000000000000 : ℝ))
      (E := (cell12918 ⟨31, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (5187628102573 / 6250000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (111278905367 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_32 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (41483948699187 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225582102411 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨32, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (41483948699187 / 50000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225582102411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_33 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82933768951101 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556396535191 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨33, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82933768951101 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556396535191 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_34 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82899664268443 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112795082333 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨34, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82899664268443 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112795082333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_35 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (1657311666393 / 2000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112797058033 / 50000000000000 : ℝ))
      (E := (cell12918 ⟨35, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (1657311666393 / 2000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (1112797058033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_36 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (8283152607413 / 10000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (222559817129 / 10000000000000 : ℝ))
      (E := (cell12918 ⟨36, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (8283152607413 / 10000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (222559817129 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_37 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (20699373125361 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225602154539 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨37, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (20699373125361 / 25000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225602154539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_38 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82763482571307 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556401545779 / 25000000000000 : ℝ))
      (E := (cell12918 ⟨38, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82763482571307 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (556401545779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12918_39 : CellCertificate 12918 (55043688163737 / 625000000000000 : ℝ) (1625972453856031 / 1000000000000000000 : ℝ) (65661333494057 / 2000000000000000 : ℝ)
    (cell12918 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · norm_num [cell12918]
  · have h := gap_lower (n := 12918) (a := (82729496253589 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225610198053 / 100000000000000 : ℝ))
      (E := (cell12918 ⟨39, by decide⟩).energy) (xi := (65661333494057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12918 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12918]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12918])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12918) (a := (82729496253589 / 100000000000000 : ℝ)) (b := (159419782133 / 100000000000000 : ℝ)) (q := (2225610198053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12918])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12918]

theorem cert12919_20 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41689647673183 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225417803509 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨20, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41689647673183 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225417803509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_21 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83344879570351 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112710893693 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨21, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83344879570351 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112710893693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_22 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (20827621985007 / 25000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556356447647 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨22, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (20827621985007 / 25000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556356447647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_23 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83276120422703 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225429816541 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨23, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83276120422703 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225429816541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_24 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (10405222123231 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445086762009 / 20000000000000 : ℝ))
      (E := (cell12919 ⟨24, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (10405222123231 / 12500000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445086762009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_25 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83207457597103 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445087566481 / 20000000000000 : ℝ))
      (E := (cell12919 ⟨25, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83207457597103 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (445087566481 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_26 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41586581112137 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (34772528561 / 1562500000000 : ℝ))
      (E := (cell12919 ⟨26, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41586581112137 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (34772528561 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_27 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (8313889083533 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (222544585743 / 10000000000000 : ℝ))
      (E := (cell12919 ⟨27, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (8313889083533 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (222544585743 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_28 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (16620928679681 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112724932379 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨28, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (16620928679681 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112724932379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_29 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (20767604970449 / 25000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112726925923 / 50000000000000 : ℝ))
      (E := (cell12919 ⟨29, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (20767604970449 / 25000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (1112726925923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_30 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83036220253961 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225457878961 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨30, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83036220253961 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225457878961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_31 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (83002044483517 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (13909136807 / 625000000000 : ℝ))
      (E := (cell12919 ⟨31, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (83002044483517 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (13909136807 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_32 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (16593578507849 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556366470899 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨32, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (16593578507849 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556366470899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_33 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (259168013719 / 312500000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225469863439 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨33, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (259168013719 / 312500000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225469863439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_34 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41449830002559 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (22254738881 / 1000000000000 : ℝ))
      (E := (cell12919 ⟨34, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41449830002559 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (22254738881 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_35 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (8286557935361 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556369474899 / 25000000000000 : ℝ))
      (E := (cell12919 ⟨35, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (8286557935361 / 10000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (556369474899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_36 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (16566304480993 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225481898301 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨36, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (16566304480993 / 20000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225481898301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_37 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (82797489128743 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (139092867773 / 6250000000000 : ℝ))
      (E := (cell12919 ⟨37, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (82797489128743 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (139092867773 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_38 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (41381739747331 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225489916447 / 100000000000000 : ℝ))
      (E := (cell12919 ⟨38, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (41381739747331 / 50000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (2225489916447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12919_39 : CellCertificate 12919 (88067197345147 / 1000000000000000 : ℝ) (325169310834701 / 200000000000000000 : ℝ) (164140328076943 / 5000000000000000 : ℝ)
    (cell12919 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · norm_num [cell12919]
  · have h := gap_lower (n := 12919) (a := (82729493472591 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (222549393557 / 10000000000000 : ℝ))
      (E := (cell12919 ⟨39, by decide⟩).energy) (xi := (164140328076943 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12919 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12919]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12919])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12919) (a := (82729493472591 / 100000000000000 : ℝ)) (b := (159407296847 / 100000000000000 : ℝ)) (q := (222549393557 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12919])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12919]

theorem cert12920_20 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41689643439513 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556325393871 / 25000000000000 : ℝ))
      (E := (cell12920 ⟨20, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41689643439513 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (556325393871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_21 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (20836217851523 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112652775577 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨21, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (20836217851523 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112652775577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_22 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (20827620019607 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278163700649 / 12500000000000 : ℝ))
      (E := (cell12920 ⟨22, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (20827620019607 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278163700649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_23 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83276112863341 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445062713197 / 20000000000000 : ℝ))
      (E := (cell12920 ⟨23, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83276112863341 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445062713197 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_24 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (5202610608019 / 6250000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445063522353 / 20000000000000 : ℝ))
      (E := (cell12920 ⟨24, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (5202610608019 / 6250000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (445063522353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_25 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41603725320479 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (89012865149 / 4000000000000 : ℝ))
      (E := (cell12920 ⟨25, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41603725320479 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (89012865149 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_26 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (20793288892277 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (6954142561 / 312500000000 : ℝ))
      (E := (cell12920 ⟨26, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (20793288892277 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (6954142561 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_27 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83138884480727 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (222532958657 / 10000000000000 : ℝ))
      (E := (cell12920 ⟨27, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83138884480727 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (222532958657 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_28 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (83104637343947 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112666795277 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨28, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (83104637343947 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112666795277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_29 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (20767603531767 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (4450675267 / 200000000000 : ℝ))
      (E := (cell12920 ⟨29, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (20767603531767 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (4450675267 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_30 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41518107399273 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112670829339 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨30, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41518107399273 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112670829339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_31 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41501019663501 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278168201129 / 12500000000000 : ℝ))
      (E := (cell12920 ⟨31, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41501019663501 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (278168201129 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_32 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (1296373245019 / 1562500000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225349661507 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨32, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (1296373245019 / 1562500000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225349661507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_33 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (20733439957531 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225353641481 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨33, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (20733439957531 / 25000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225353641481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_34 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (82899655742823 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225357666959 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨34, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (82899655742823 / 100000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225357666959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_35 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (16573115077713 / 20000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (55634041999 / 2500000000000 : ℝ))
      (E := (cell12920 ⟨35, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (16573115077713 / 20000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (55634041999 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_36 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41415759368379 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112682840429 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨36, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41415759368379 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112682840429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_37 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41398742878483 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225369669801 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨37, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41398742878483 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225369669801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_38 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (16552695283781 / 20000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225373705441 / 100000000000000 : ℝ))
      (E := (cell12920 ⟨38, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (16552695283781 / 20000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (2225373705441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12920_39 : CellCertificate 12920 (220161235073741 / 2500000000000000 : ℝ) (1625720673986391 / 1000000000000000000 : ℝ) (164127324499799 / 5000000000000000 : ℝ)
    (cell12920 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · norm_num [cell12920]
  · have h := gap_lower (n := 12920) (a := (41364745346223 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112688835033 / 50000000000000 : ℝ))
      (E := (cell12920 ⟨39, by decide⟩).energy) (xi := (164127324499799 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12920 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12920]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12920])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12920) (a := (41364745346223 / 50000000000000 : ℝ)) (b := (79697406763 / 50000000000000 : ℝ)) (q := (1112688835033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12920])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12920]

theorem cert12921_20 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83379278413217 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225185343743 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨20, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83379278413217 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225185343743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_21 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83344863243327 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225189369567 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨21, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83344863243327 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225189369567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_22 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83310472218287 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (139074584863 / 6250000000000 : ℝ))
      (E := (cell12921 ⟨22, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83310472218287 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (139074584863 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_23 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41638052652701 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445039474039 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨23, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41638052652701 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445039474039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_24 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83241762472147 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225201409917 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨24, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83241762472147 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225201409917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_25 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83207443686163 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445041084303 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨25, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83207443686163 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445041084303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_26 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41586574457629 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (55630235191 / 2500000000000 : ℝ))
      (E := (cell12921 ⟨26, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41586574457629 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (55630235191 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_27 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41569439063701 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225213429179 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨27, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41569439063701 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225213429179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_28 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83104631290733 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112608714951 / 50000000000000 : ℝ))
      (E := (cell12921 ⟨28, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83104631290733 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112608714951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_29 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41535204186773 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225221411771 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨29, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41535204186773 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225221411771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_30 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (83036209344303 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (278153179381 / 12500000000000 : ℝ))
      (E := (cell12921 ⟨30, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (83036209344303 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (278153179381 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_31 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (10375254271453 / 12500000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225229442747 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨31, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (10375254271453 / 12500000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225229442747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_32 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82967882824287 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (139077089759 / 6250000000000 : ℝ))
      (E := (cell12921 ⟨32, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82967882824287 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (139077089759 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_33 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82933755271233 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (278154684361 / 12500000000000 : ℝ))
      (E := (cell12921 ⟨33, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82933755271233 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (278154684361 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_34 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82899651481557 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225241442617 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨34, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82899651481557 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225241442617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_35 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (82865571424513 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (55631136429 / 2500000000000 : ℝ))
      (E := (cell12921 ⟨35, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (82865571424513 / 100000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (55631136429 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_36 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (8283151506951 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445049892057 / 20000000000000 : ℝ))
      (E := (cell12921 ⟨36, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (8283151506951 / 10000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (445049892057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_37 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (1293710662283 / 1562500000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225253452141 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨37, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (1293710662283 / 1562500000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225253452141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_38 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (20690868336009 / 25000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225257491379 / 100000000000000 : ℝ))
      (E := (cell12921 ⟨38, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (20690868336009 / 25000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (2225257491379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12921_39 : CellCertificate 12921 (440308955574669 / 5000000000000000 : ℝ) (1625594813290161 / 1000000000000000000 : ℝ) (20514290375397 / 625000000000000 : ℝ)
    (cell12921 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · norm_num [cell12921]
  · have h := gap_lower (n := 12921) (a := (41364743956577 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112630730143 / 50000000000000 : ℝ))
      (E := (cell12921 ⟨39, by decide⟩).energy) (xi := (20514290375397 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12921 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12921]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12921])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12921) (a := (41364743956577 / 50000000000000 : ℝ)) (b := (15938233217 / 10000000000000 : ℝ)) (q := (1112630730143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12921])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12921]

theorem cert12922_20 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (41689634974469 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225069166587 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨20, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (41689634974469 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225069166587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_21 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83344855082057 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225073184301 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨21, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83344855082057 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225073184301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_22 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (20827616089901 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225077223477 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨22, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (20827616089901 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225077223477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_23 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (20819024437221 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556270307293 / 25000000000000 : ℝ))
      (E := (cell12922 ⟨23, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (20819024437221 / 25000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556270307293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_24 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (665934041739 / 800000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278135650563 / 12500000000000 : ℝ))
      (E := (cell12922 ⟨24, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (665934041739 / 800000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278135650563 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_25 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (41603718366359 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (89003568431 / 4000000000000 : ℝ))
      (E := (cell12922 ⟨25, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (41603718366359 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (89003568431 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_26 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83173142262721 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225093250709 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨26, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83173142262721 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225093250709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_27 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83138871775357 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225097209867 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨27, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83138871775357 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225097209867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_28 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (83104625238761 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225101265831 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨28, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (83104625238761 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225101265831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_29 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (5191900163827 / 6250000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (139069077823 / 6250000000000 : ℝ))
      (E := (cell12922 ⟨29, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (5191900163827 / 6250000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (139069077823 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_30 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (2594881371601 / 3125000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556277316651 / 25000000000000 : ℝ))
      (E := (cell12922 ⟨30, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (2594881371601 / 3125000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556277316651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_31 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (4150101450869 / 5000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225113273153 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨31, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (4150101450869 / 5000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225113273153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_32 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82967877968459 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112558633043 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨32, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82967877968459 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112558633043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_33 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82933750713407 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225121246453 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨33, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82933750713407 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225121246453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_34 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82899647221321 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225125273701 / 100000000000000 : ℝ))
      (E := (cell12922 ⟨34, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82899647221321 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (2225125273701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_35 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (5179097966341 / 6250000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556282322461 / 25000000000000 : ℝ))
      (E := (cell12922 ⟨35, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (5179097966341 / 6250000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (556282322461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_36 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82831511403221 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278141661907 / 12500000000000 : ℝ))
      (E := (cell12922 ⟨36, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82831511403221 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (278141661907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_37 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (82797479016181 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112568645043 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨37, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (82797479016181 / 100000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112568645043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_38 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (16552694054011 / 20000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112570666491 / 50000000000000 : ℝ))
      (E := (cell12922 ⟨38, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (16552694054011 / 20000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (1112570666491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12922_39 : CellCertificate 12922 (176118177202731 / 2000000000000000 : ℝ) (1625468972080289 / 1000000000000000000 : ℝ) (328202647173081 / 10000000000000000 : ℝ)
    (cell12922 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · norm_num [cell12922]
  · have h := gap_lower (n := 12922) (a := (41364742567357 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (222514530623 / 10000000000000 : ℝ))
      (E := (cell12922 ⟨39, by decide⟩).energy) (xi := (328202647173081 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12922 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12922]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12922])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12922) (a := (41364742567357 / 50000000000000 : ℝ)) (b := (159369852779 / 100000000000000 : ℝ)) (q := (222514530623 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12922])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12922]

theorem cert12923_20 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (8337926148619 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224953044017 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨20, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (8337926148619 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224953044017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_21 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83344846922281 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224957053683 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨21, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83344846922281 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224957053683 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_22 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (41655228251189 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224961027161 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨22, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (41655228251189 / 50000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224961027161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_23 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83276090193789 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112482542273 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨23, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83276090193789 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112482542273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_24 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (8324174796399 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224969053917 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨24, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (8324174796399 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224969053917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_25 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83207429780623 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224973054923 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨25, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83207429780623 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224973054923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_26 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83173135611499 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556244272571 / 25000000000000 : ℝ))
      (E := (cell12923 ⟨26, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83173135611499 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556244272571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_27 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83138865424589 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556245276007 / 25000000000000 : ℝ))
      (E := (cell12923 ⟨27, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83138865424589 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (556245276007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_28 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83104619188031 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112492549171 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨28, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83104619188031 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112492549171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_29 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (664563174961 / 800000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224989075183 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨29, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (664563174961 / 800000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2224989075183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_30 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83036198439331 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (444998618963 / 20000000000000 : ℝ))
      (E := (cell12923 ⟨30, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83036198439331 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (444998618963 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_31 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (83002023864273 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (278124637531 / 12500000000000 : ℝ))
      (E := (cell12923 ⟨31, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (83002023864273 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (278124637531 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_32 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (8296787311373 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225001092757 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨32, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (8296787311373 / 10000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225001092757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_33 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (20733436539161 / 25000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225005131991 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨33, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (20733436539161 / 25000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225005131991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_34 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82899642962113 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (445001820317 / 20000000000000 : ℝ))
      (E := (cell12923 ⟨34, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82899642962113 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (445001820317 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_35 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82865563499391 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112506559683 / 50000000000000 : ℝ))
      (E := (cell12923 ⟨35, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82865563499391 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (1112506559683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_36 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82831507737889 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225017127101 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨36, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82831507737889 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225017127101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_37 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82797475647173 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225021124939 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨37, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82797475647173 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225021124939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_38 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82763467196961 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225025171529 / 100000000000000 : ℝ))
      (E := (cell12923 ⟨38, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82763467196961 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (2225025171529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12923_39 : CellCertificate 12923 (880563864886981 / 10000000000000000 : ℝ) (1625343150352249 / 1000000000000000000 : ℝ) (328176652498717 / 10000000000000000 : ℝ)
    (cell12923 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · norm_num [cell12923]
  · have h := gap_lower (n := 12923) (a := (82729482357127 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (445005829831 / 20000000000000 : ℝ))
      (E := (cell12923 ⟨39, by decide⟩).energy) (xi := (328176652498717 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12923 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12923]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12923])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12923) (a := (82729482357127 / 100000000000000 : ℝ)) (b := (19919671919 / 12500000000000 : ℝ)) (q := (445005829831 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12923])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12923]

theorem cert12924_20 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83379253024971 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444967383547 / 20000000000000 : ℝ))
      (E := (cell12924 ⟨20, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83379253024971 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (444967383547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_21 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83344838763999 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224840919389 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨21, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83344838763999 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224840919389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_22 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83310448646611 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112422471949 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨22, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83310448646611 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112422471949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_23 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (16655216528023 / 20000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224848936319 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨23, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (16655216528023 / 20000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224848936319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_24 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (8324174071199 / 10000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (27810661977 / 1250000000000 : ℝ))
      (E := (cell12924 ⟨24, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (8324174071199 / 10000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (27810661977 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_25 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41603711414939 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224856953961 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨25, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41603711414939 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224856953961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_26 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (8317312896159 / 10000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (222486092637 / 10000000000000 : ℝ))
      (E := (cell12924 ⟨26, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (8317312896159 / 10000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (222486092637 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_27 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83138859075099 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (139054058517 / 6250000000000 : ℝ))
      (E := (cell12924 ⟨27, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83138859075099 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (139054058517 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_28 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83104613138543 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224868985923 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨28, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83104613138543 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224868985923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_29 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (2595949722507 / 3125000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (278109120041 / 12500000000000 : ℝ))
      (E := (cell12924 ⟨29, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (2595949722507 / 3125000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (278109120041 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_30 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (83036192988601 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (278109622277 / 12500000000000 : ℝ))
      (E := (cell12924 ⟨30, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (83036192988601 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (278109622277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_31 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (830020187123 / 1000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112440491297 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨31, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (830020187123 / 1000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112440491297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_32 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82967868260101 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224884974737 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨32, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82967868260101 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224884974737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_33 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41466870800473 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112444507147 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨33, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41466870800473 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112444507147 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_34 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (41449819351967 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224892984897 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨34, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (41449819351967 / 50000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224892984897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_35 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (1035819494229 / 1250000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (278112125547 / 12500000000000 : ℝ))
      (E := (cell12924 ⟨35, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (1035819494229 / 1250000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (278112125547 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_36 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (20707876018379 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112450507247 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨36, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (20707876018379 / 25000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112450507247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_37 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (82797472279087 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224905015401 / 100000000000000 : ℝ))
      (E := (cell12924 ⟨37, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (82797472279087 / 100000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (2224905015401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_38 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (16552692824951 / 20000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112454503511 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨38, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (16552692824951 / 20000000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112454503511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

theorem cert12924_39 : CellCertificate 12924 (880536847768379 / 10000000000000000 : ℝ) (812608674050759 / 500000000000000000 : ℝ) (82037665495549 / 2500000000000000 : ℝ)
    (cell12924 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · norm_num [cell12924]
  · have h := gap_lower (n := 12924) (a := (10341184947549 / 12500000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112456523903 / 50000000000000 : ℝ))
      (E := (cell12924 ⟨39, by decide⟩).energy) (xi := (82037665495549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12924 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12924]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12924])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12924) (a := (10341184947549 / 12500000000000 : ℝ)) (b := (9959056243 / 6250000000000 : ℝ)) (q := (1112456523903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12924])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12924]

end BstLean.Part268
