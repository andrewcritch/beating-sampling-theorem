import BstLean.Part268CellShard12Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12650_0 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (42038374936757 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (282206254709 / 12500000000000 : ℝ))
      (E := (cell12650 ⟨0, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (42038374936757 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (282206254709 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_1 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (1680835176457 / 2000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257654051647 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨1, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (1680835176457 / 2000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257654051647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_2 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (21001698182293 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257658053391 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨2, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (21001698182293 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257658053391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_3 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41985925777963 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564415512967 / 25000000000000 : ℝ))
      (E := (cell12650 ⟨3, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41985925777963 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (564415512967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_4 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41968467633377 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128833027889 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨4, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41968467633377 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128833027889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_5 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (5243877739093 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128835036783 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨5, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (5243877739093 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128835036783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_6 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (1677343543923 / 2000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128837027737 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨6, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (1677343543923 / 2000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128837027737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_7 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (10479041917869 / 12500000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128839033667 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨7, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (10479041917869 / 12500000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128839033667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_8 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83797518230293 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257682058831 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨8, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83797518230293 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257682058831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_9 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41881362911379 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257686037321 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨9, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41881362911379 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257686037321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_10 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41863979042559 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257690067947 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨10, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41863979042559 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257690067947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_11 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83693214982329 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451538808301 / 20000000000000 : ℝ))
      (E := (cell12650 ⟨11, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83693214982329 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451538808301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_12 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83658496479527 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257698080701 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨12, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83658496479527 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257698080701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_13 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (5226487658877 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257702075741 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨13, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (5226487658877 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257702075741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_14 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (5224320820959 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128853016331 / 50000000000000 : ℝ))
      (E := (cell12650 ⟨14, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (5224320820959 / 6250000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (1128853016331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_15 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83554488225143 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (70553439799 / 3125000000000 : ℝ))
      (E := (cell12650 ⟨15, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83554488225143 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (70553439799 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_16 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (16703973555457 / 20000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451542805921 / 20000000000000 : ℝ))
      (E := (cell12650 ⟨16, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (16703973555457 / 20000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451542805921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_17 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (41742635878903 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451543616123 / 20000000000000 : ℝ))
      (E := (cell12650 ⟨17, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (41742635878903 / 50000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (451543616123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_18 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (20862675033229 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257722057117 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨18, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (20862675033229 / 25000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257722057117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12650_19 : CellCertificate 12650 (222023171386227 / 2500000000000000 : ℝ) (103776956522217 / 62500000000000000 : ℝ) (335431294621171 / 10000000000000000 : ℝ)
    (cell12650 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · norm_num [cell12650]
  · have h := gap_lower (n := 12650) (a := (83416152869001 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257726080357 / 100000000000000 : ℝ))
      (E := (cell12650 ⟨19, by decide⟩).energy) (xi := (335431294621171 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12650 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12650]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12650])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12650) (a := (83416152869001 / 100000000000000 : ℝ)) (b := (81419143749 / 50000000000000 : ℝ)) (q := (2257726080357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12650])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12650]

theorem cert12651_0 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (4203836731273 / 5000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (56438138403 / 2500000000000 : ℝ))
      (E := (cell12651 ⟨0, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (4203836731273 / 5000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (56438138403 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_1 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (42020871948401 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564382392767 / 25000000000000 : ℝ))
      (E := (cell12651 ⟨1, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (42020871948401 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564382392767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_2 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (84006778124673 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257533536711 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨2, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (84006778124673 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257533536711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_3 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (83971837272523 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257537557691 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨3, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (83971837272523 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257537557691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_4 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (83936921303993 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257541584879 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨4, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (83936921303993 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257541584879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_5 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (20975507545729 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128772784399 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨5, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (20975507545729 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128772784399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_6 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (16773432774663 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (225754957551 / 10000000000000 : ℝ))
      (E := (cell12651 ⟨6, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (16773432774663 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (225754957551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_7 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (20958080584851 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (70548548593 / 3125000000000 : ℝ))
      (E := (cell12651 ⟨7, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (20958080584851 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (70548548593 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_8 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (41898752772791 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257557572797 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨8, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (41898752772791 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257557572797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_9 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (16752542691287 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128780789191 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨9, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (16752542691287 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128780789191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_10 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (163531144603 / 195312500000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (141097848677 / 6250000000000 : ℝ))
      (E := (cell12651 ⟨10, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (163531144603 / 195312500000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (141097848677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_11 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (1046165040643 / 1250000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257569580999 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨11, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (1046165040643 / 1250000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257569580999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_12 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (41829242532843 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (11287867667 / 500000000000 : ℝ))
      (E := (cell12651 ⟨12, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (41829242532843 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (11287867667 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_13 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (41811895722397 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257577558537 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨13, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (41811895722397 / 50000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257577558537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_14 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (16717824470853 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257581546321 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨14, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (16717824470853 / 20000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257581546321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_15 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (4177723887989 / 5000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257585560697 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨15, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (4177723887989 / 5000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257585560697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_16 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (20879964406799 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257589549103 / 100000000000000 : ℝ))
      (E := (cell12651 ⟨16, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (20879964406799 / 25000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (2257589549103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_17 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (83485261922549 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128796787521 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨17, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (83485261922549 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128796787521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_18 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (83450690612051 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564399381797 / 25000000000000 : ℝ))
      (E := (cell12651 ⟨18, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (83450690612051 / 100000000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (564399381797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12651_19 : CellCertificate 12651 (888064538473921 / 10000000000000000 : ℝ) (1660300012018641 / 1000000000000000000 : ℝ) (67080825567099 / 2000000000000000 : ℝ)
    (cell12651 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · norm_num [cell12651]
  · have h := gap_lower (n := 12651) (a := (10427017957761 / 12500000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128800792519 / 50000000000000 : ℝ))
      (E := (cell12651 ⟨19, by decide⟩).energy) (xi := (67080825567099 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12651 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12651]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12651])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12651) (a := (10427017957761 / 12500000000000 : ℝ)) (b := (6513010301 / 4000000000000 : ℝ)) (q := (1128800792519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12651])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12651]

theorem cert12652_0 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (84076719379819 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (225740108759 / 10000000000000 : ℝ))
      (E := (cell12652 ⟨0, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (84076719379819 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (225740108759 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_1 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (10505216121641 / 12500000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128702542873 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨1, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (10505216121641 / 12500000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128702542873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_2 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (8400676352251 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (112870453659 / 5000000000000 : ℝ))
      (E := (cell12652 ⟨2, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (8400676352251 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (112870453659 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_3 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (10496477873927 / 12500000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257413116727 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨3, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (10496477873927 / 12500000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257413116727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_4 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (655757088621 / 781250000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (28217713867 / 1250000000000 : ℝ))
      (E := (cell12652 ⟨4, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (655757088621 / 781250000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (28217713867 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_5 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83902016542561 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564355279343 / 25000000000000 : ℝ))
      (E := (cell12652 ⟨5, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83902016542561 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564355279343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_6 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83867150552659 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564356272751 / 25000000000000 : ℝ))
      (E := (cell12652 ⟨6, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83867150552659 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (564356272751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_7 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (16766461867599 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128714548043 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨7, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (16766461867599 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128714548043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_8 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83797492862971 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128716541151 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨8, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83797492862971 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128716541151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_9 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41881350546087 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (112871855751 / 5000000000000 : ℝ))
      (E := (cell12652 ⟨9, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41881350546087 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (112871855751 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_10 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83727933990377 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128720542667 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨10, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83727933990377 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128720542667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_11 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (16738638304507 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257445116151 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨11, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (16738638304507 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257445116151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_12 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (8365847365379 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257449097969 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨12, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (8365847365379 / 10000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257449097969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_13 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83623780349463 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257453095179 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨13, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83623780349463 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257453095179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_14 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41794555787527 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257457113889 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨14, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41794555787527 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257457113889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_15 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (41777233648123 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (11287305509 / 500000000000 : ℝ))
      (E := (cell12652 ⟨15, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (41777233648123 / 50000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (11287305509 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_16 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83519847478897 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257465064457 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨16, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83519847478897 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257465064457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_17 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (16697050417809 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257469065363 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨17, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (16697050417809 / 20000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257469065363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_18 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (83450681092901 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128736554823 / 50000000000000 : ℝ))
      (E := (cell12652 ⟨18, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (83450681092901 / 100000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (1128736554823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12652_19 : CellCertificate 12652 (888036395676741 / 10000000000000000 : ℝ) (830084370221529 / 500000000000000000 : ℝ) (335376965515441 / 10000000000000000 : ℝ)
    (cell12652 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · norm_num [cell12652]
  · have h := gap_lower (n := 12652) (a := (20854033614213 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257477085691 / 100000000000000 : ℝ))
      (E := (cell12652 ⟨19, by decide⟩).energy) (xi := (335376965515441 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12652 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12652]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12652])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12652) (a := (20854033614213 / 25000000000000 : ℝ)) (b := (40703057413 / 25000000000000 : ℝ)) (q := (2257477085691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12652])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12652]

theorem cert12653_0 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (5254794008537 / 6250000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (28215958651 / 1250000000000 : ℝ))
      (E := (cell12653 ⟨0, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (5254794008537 / 6250000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (28215958651 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_1 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (84041714051827 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257280653509 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨1, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (84041714051827 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257280653509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_2 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (84006748922681 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128642331399 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨2, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (84006748922681 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128642331399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_3 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83971808712603 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257288671101 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨3, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83971808712603 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257288671101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_4 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83936893385239 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451458537423 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨4, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83936893385239 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451458537423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_5 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83902002904423 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128648330681 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨5, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83902002904423 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128648330681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_6 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (4193356861709 / 5000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257300659901 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨6, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (4193356861709 / 5000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257300659901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_7 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41916148169363 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257304690661 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨7, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41916148169363 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257304690661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_8 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83797480182461 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451461729067 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨8, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83797480182461 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451461729067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_9 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41881344364987 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451462529447 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨9, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41881344364987 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451462529447 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_10 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83727921946039 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257316645493 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨10, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83727921946039 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257316645493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_11 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (16738635959123 / 20000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128660323479 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨11, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (16738635959123 / 20000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128660323479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_12 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (16339543407 / 19531250000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (282165582279 / 12500000000000 : ℝ))
      (E := (cell12653 ⟨12, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (16339543407 / 19531250000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (282165582279 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_13 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41811884628019 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451465737133 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨13, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41811884628019 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451465737133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_14 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83589100797711 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257332677231 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨14, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83589100797711 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257332677231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_15 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (41777228417271 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (564334159679 / 25000000000000 : ℝ))
      (E := (cell12653 ⟨15, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (41777228417271 / 50000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (564334159679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_16 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (8351983733239 / 10000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (282167586503 / 12500000000000 : ℝ))
      (E := (cell12653 ⟨16, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (8351983733239 / 10000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (282167586503 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_17 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83485242257293 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451468933597 / 20000000000000 : ℝ))
      (E := (cell12653 ⟨17, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83485242257293 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (451468933597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_18 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (10431333946933 / 12500000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128674344019 / 50000000000000 : ℝ))
      (E := (cell12653 ⟨18, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (10431333946933 / 12500000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (1128674344019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12653_19 : CellCertificate 12653 (888008257152349 / 10000000000000000 : ℝ) (1660037489623799 / 1000000000000000000 : ℝ) (167674903829903 / 5000000000000000 : ℝ)
    (cell12653 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · norm_num [cell12653]
  · have h := gap_lower (n := 12653) (a := (83416125253291 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257352640567 / 100000000000000 : ℝ))
      (E := (cell12653 ⟨19, by decide⟩).energy) (xi := (167674903829903 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12653 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12653]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12653])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12653) (a := (83416125253291 / 100000000000000 : ℝ)) (b := (162799203881 / 100000000000000 : ℝ)) (q := (2257352640567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12653])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12653]

theorem cert12654_0 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (84076688895777 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (225715229179 / 10000000000000 : ℝ))
      (E := (cell12654 ⟨0, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (84076688895777 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (225715229179 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_1 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (840416991329 / 1000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (56428906859 / 2500000000000 : ℝ))
      (E := (cell12654 ⟨1, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (840416991329 / 1000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (56428906859 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_2 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (16801346865037 / 20000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (70536259549 / 3125000000000 : ℝ))
      (E := (cell12654 ⟨2, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (16801346865037 / 20000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (70536259549 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_3 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41985897218043 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257164278689 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨3, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41985897218043 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257164278689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_4 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41968439714623 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (9028673041 / 400000000000 : ℝ))
      (E := (cell12654 ⟨4, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41968439714623 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (9028673041 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_5 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83901989268501 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451434451739 / 20000000000000 : ℝ))
      (E := (cell12654 ⟨5, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83901989268501 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451434451739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_6 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83867123917879 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564294070551 / 25000000000000 : ℝ))
      (E := (cell12654 ⟨6, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83867123917879 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564294070551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_7 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41916141670797 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128590140369 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨7, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41916141670797 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128590140369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_8 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (1675949350081 / 2000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257184261901 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨8, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (1675949350081 / 2000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257184261901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_9 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (16752535273967 / 20000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128594145531 / 50000000000000 : ℝ))
      (E := (cell12654 ⟨9, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (16752535273967 / 20000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (1128594145531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_10 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (20931977475931 / 25000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (225719225931 / 10000000000000 : ℝ))
      (E := (cell12654 ⟨10, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (20931977475931 / 25000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (225719225931 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_11 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83693168070677 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257196289551 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨11, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83693168070677 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257196289551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_12 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41829225417917 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257200272281 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨12, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41829225417917 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257200272281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_13 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83623758164519 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257204271891 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨13, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83623758164519 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257204271891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_14 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (16717818004447 / 20000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451441658897 / 20000000000000 : ℝ))
      (E := (cell12654 ⟨14, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (16717818004447 / 20000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451441658897 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_15 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41777223187333 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564303071941 / 25000000000000 : ℝ))
      (E := (cell12654 ⟨15, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41777223187333 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564303071941 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_16 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83519827187673 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257216257269 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨16, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83519827187673 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257216257269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_17 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83485232427293 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257220266503 / 100000000000000 : ℝ))
      (E := (cell12654 ⟨17, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83485232427293 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (2257220266503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_18 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (83450662059741 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451444852473 / 20000000000000 : ℝ))
      (E := (cell12654 ⟨18, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (83450662059741 / 100000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (451444852473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12654_19 : CellCertificate 12654 (221995030724931 / 2500000000000000 : ℝ) (829953129777971 / 500000000000000000 : ℝ) (33532265426739 / 1000000000000000 : ℝ)
    (cell12654 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · norm_num [cell12654]
  · have h := gap_lower (n := 12654) (a := (41708058025703 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564307062417 / 25000000000000 : ℝ))
      (E := (cell12654 ⟨19, by decide⟩).energy) (xi := (33532265426739 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12654 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12654]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12654])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12654) (a := (41708058025703 / 50000000000000 : ℝ)) (b := (162786180209 / 100000000000000 : ℝ)) (q := (564307062417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12654])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12654]

theorem cert12655_0 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (84076673657373 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (90281117781 / 4000000000000 : ℝ))
      (E := (cell12655 ⟨0, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (84076673657373 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (90281117781 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_1 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (16808336843269 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257031948299 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨1, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (16808336843269 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257031948299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_2 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (84006719730023 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257035943637 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨2, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (84006719730023 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257035943637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_3 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (41985890080931 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257039939493 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨3, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (41985890080931 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257039939493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_4 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (83936865475507 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451408788913 / 20000000000000 : ℝ))
      (E := (cell12655 ⟨4, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (83936865475507 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451408788913 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_5 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20975493908699 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257047909369 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨5, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20975493908699 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257047909369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_6 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (16773422120751 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128525949983 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨6, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (16773422120751 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128525949983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_7 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (83832270346601 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257055924283 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨7, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (83832270346601 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257055924283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_8 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (83797454827737 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257059932001 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨8, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (83797454827737 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257059932001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_9 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (16752532802351 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257063930469 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨9, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (16752532802351 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257063930469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_10 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (8372789786343 / 10000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257067926787 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨10, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (8372789786343 / 10000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257067926787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_11 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (41846578173861 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257071927803 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨11, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (41846578173861 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257071927803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_12 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20914609857443 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564268985029 / 25000000000000 : ℝ))
      (E := (cell12655 ⟨12, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20914609857443 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564268985029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_13 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (16724749414981 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451415982393 / 20000000000000 : ℝ))
      (E := (cell12655 ⟨13, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (16724749414981 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451415982393 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_14 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (41794539624313 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257083907517 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨14, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (41794539624313 / 50000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257083907517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_15 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (83554435916619 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564271983157 / 25000000000000 : ℝ))
      (E := (cell12655 ⟨15, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (83554435916619 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (564271983157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_16 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (16703963408949 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257091934731 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨16, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (16703963408949 / 20000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257091934731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_17 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20871305649761 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128547959561 / 50000000000000 : ℝ))
      (E := (cell12655 ⟨17, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20871305649761 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (1128547959561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_18 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (83450652545731 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257099949083 / 100000000000000 : ℝ))
      (E := (cell12655 ⟨18, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (83450652545731 / 100000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (2257099949083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12655_19 : CellCertificate 12655 (110993999114731 / 1250000000000000 : ℝ) (829887525117283 / 500000000000000000 : ℝ) (335295505336993 / 10000000000000000 : ℝ)
    (cell12655 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · norm_num [cell12655]
  · have h := gap_lower (n := 12655) (a := (20854026712799 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451420782599 / 20000000000000 : ℝ))
      (E := (cell12655 ⟨19, by decide⟩).energy) (xi := (335295505336993 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12655 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12655]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12655])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12655) (a := (20854026712799 / 25000000000000 : ℝ)) (b := (162773158637 / 100000000000000 : ℝ)) (q := (451420782599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12655])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12655]

theorem cert12656_0 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (84076658421381 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (14105647453 / 625000000000 : ℝ))
      (E := (cell12656 ⟨0, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (84076658421381 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (14105647453 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_1 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (42020834651081 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (902763047 / 40000000000 : ℝ))
      (E := (cell12656 ⟨1, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (42020834651081 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (902763047 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_2 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (42003352568597 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (112845581743 / 5000000000000 : ℝ))
      (E := (cell12656 ⟨2, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (42003352568597 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (112845581743 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_3 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20992941472483 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256915595639 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨3, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20992941472483 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256915595639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_4 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83936851524023 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256919624261 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨4, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83936851524023 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256919624261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_5 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (16780392400661 / 20000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256923613389 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨5, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (16780392400661 / 20000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256923613389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_6 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (41933548645903 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564231907271 / 25000000000000 : ℝ))
      (E := (cell12656 ⟨6, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (41933548645903 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564231907271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_7 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (5239516084609 / 6250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (22569316213 / 1000000000000 : ℝ))
      (E := (cell12656 ⟨7, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (5239516084609 / 6250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (22569316213 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_8 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20949360538381 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (56423389941 / 2500000000000 : ℝ))
      (E := (cell12656 ⟨8, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20949360538381 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (56423389941 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_9 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (10470331456967 / 12500000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256939623473 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨9, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (10470331456967 / 12500000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256939623473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_10 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83727885825157 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451388717977 / 20000000000000 : ℝ))
      (E := (cell12656 ⟨10, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83727885825157 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451388717977 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_11 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83693144626749 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256947619779 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨11, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83693144626749 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256947619779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_12 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83658428025653 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256951603651 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨12, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83658428025653 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256951603651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_13 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83623735987197 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (17632465671 / 781250000000 : ℝ))
      (E := (cell12656 ⟨13, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83623735987197 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (17632465671 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_14 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (20897267119221 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451391926519 / 20000000000000 : ℝ))
      (E := (cell12656 ⟨14, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (20897267119221 / 25000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (451391926519 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_15 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (208886063651 / 250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256963631469 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨15, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (208886063651 / 250000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256963631469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_16 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83519806903607 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256967608051 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨16, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83519806903607 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256967608051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_17 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (83485212772547 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256971625841 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨17, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (83485212772547 / 100000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256971625841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_18 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (41725321516717 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256975631737 / 100000000000000 : ℝ))
      (E := (cell12656 ⟨18, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (41725321516717 / 50000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (2256975631737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12656_19 : CellCertificate 12656 (8879238672057 / 100000000000000 : ℝ) (6638575446619 / 4000000000000000 : ℝ) (41908545108427 / 1250000000000000 : ℝ)
    (cell12656 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · norm_num [cell12656]
  · have h := gap_lower (n := 12656) (a := (4170804882633 / 5000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564244907637 / 25000000000000 : ℝ))
      (E := (cell12656 ⟨19, by decide⟩).energy) (xi := (41908545108427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12656 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12656]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12656])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12656) (a := (4170804882633 / 5000000000000 : ℝ)) (b := (40690034791 / 25000000000000 : ℝ)) (q := (564244907637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12656])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12656]

theorem cert12657_0 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (420383215939 / 500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256779351269 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨0, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (420383215939 / 500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256779351269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_1 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (1680833087807 / 2000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256783339793 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨1, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (1680833087807 / 2000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256783339793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_2 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (10500836318337 / 12500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256787321387 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨2, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (10500836318337 / 12500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256787321387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_3 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (16794350324059 / 20000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256791305003 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨3, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (16794350324059 / 20000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256791305003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_4 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (83936837574793 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256795357239 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨4, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (83936837574793 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256795357239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_5 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (83901948374029 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256799312833 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨5, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (83901948374029 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256799312833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_6 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41933541991017 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (35262552401 / 1562500000000 : ℝ))
      (E := (cell12657 ⟨6, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41933541991017 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (35262552401 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_7 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (3353289774521 / 4000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256807313819 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨7, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (3353289774521 / 4000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256807313819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_8 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (1309334835647 / 1562500000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256811316817 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨8, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (1309334835647 / 1562500000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256811316817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_9 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (3350505572071 / 4000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256815312061 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨9, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (3350505572071 / 4000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256815312061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_10 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (16745574757781 / 20000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451363861329 / 20000000000000 : ℝ))
      (E := (cell12657 ⟨10, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (16745574757781 / 20000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451363861329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_11 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (83693132907757 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128411653709 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨11, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (83693132907757 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128411653709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_12 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (41829208311739 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128413660487 / 50000000000000 : ℝ))
      (E := (cell12657 ⟨12, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (41829208311739 / 50000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (1128413660487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_13 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (5226482806337 / 6250000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451366270733 / 20000000000000 : ℝ))
      (E := (cell12657 ⟨13, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (5226482806337 / 6250000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451366270733 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_14 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (83589057707007 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451367070691 / 20000000000000 : ℝ))
      (E := (cell12657 ⟨14, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (83589057707007 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (451367070691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_15 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (10444301875751 / 12500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (225683932613 / 10000000000000 : ℝ))
      (E := (cell12657 ⟨15, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (10444301875751 / 12500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (225683932613 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_16 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (83519796764259 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256843335411 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨16, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (83519796764259 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256843335411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_17 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (417426014739 / 500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (112842366423 / 5000000000000 : ℝ))
      (E := (cell12657 ⟨17, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (417426014739 / 500000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (112842366423 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_18 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (1669012670457 / 2000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (282106413791 / 12500000000000 : ℝ))
      (E := (cell12657 ⟨18, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (1669012670457 / 2000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (282106413791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12657_19 : CellCertificate 12657 (110986968220283 / 1250000000000000 : ℝ) (829756346905789 / 500000000000000000 : ℝ) (167620610428729 / 5000000000000000 : ℝ)
    (cell12657 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · norm_num [cell12657]
  · have h := gap_lower (n := 12657) (a := (83416088455799 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256855344079 / 100000000000000 : ℝ))
      (E := (cell12657 ⟨19, by decide⟩).energy) (xi := (167620610428729 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12657 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12657]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12657])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12657) (a := (83416088455799 / 100000000000000 : ℝ)) (b := (162747121789 / 100000000000000 : ℝ)) (q := (2256855344079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12657])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12657]

theorem cert12658_0 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (21019156989157 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128327552641 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨0, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (21019156989157 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128327552641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_1 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (84041639480909 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128329557589 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨1, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (84041639480909 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128329557589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_2 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (84006675958531 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564165765267 / 25000000000000 : ℝ))
      (E := (cell12658 ⟨2, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (84006675958531 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564165765267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_3 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (1679434747059 / 2000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564166766897 / 25000000000000 : ℝ))
      (E := (cell12658 ⟨3, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (1679434747059 / 2000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564166766897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_4 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (10492102953477 / 12500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256671085601 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨4, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (10492102953477 / 12500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256671085601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_5 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (10487741843371 / 12500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128337532811 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨5, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (10487741843371 / 12500000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128337532811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_6 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83867070674437 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564169768427 / 25000000000000 : ℝ))
      (E := (cell12658 ⟨6, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83867070674437 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564169768427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_7 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41916115687221 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256683059813 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨7, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41916115687221 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256683059813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_8 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (8379741681139 / 10000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256687089531 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨8, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (8379741681139 / 10000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256687089531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_9 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83762626949873 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (451338222453 / 20000000000000 : ℝ))
      (E := (cell12658 ⟨9, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83762626949873 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (451338222453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_10 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (5232991359667 / 6250000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564173769267 / 25000000000000 : ℝ))
      (E := (cell12658 ⟨10, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (5232991359667 / 6250000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (564173769267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_11 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83693121190747 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128349553423 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨11, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83693121190747 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128349553423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_12 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (16731681044649 / 20000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (282087886511 / 12500000000000 : ℝ))
      (E := (cell12658 ⟨12, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (16731681044649 / 20000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (282087886511 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_13 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (20905928454373 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128353548591 / 50000000000000 : ℝ))
      (E := (cell12658 ⟨13, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (20905928454373 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (1128353548591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_14 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (20897261734749 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (141044441881 / 6250000000000 : ℝ))
      (E := (cell12658 ⟨14, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (20897261734749 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (141044441881 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_15 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83554404553443 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (225671507477 / 10000000000000 : ℝ))
      (E := (cell12658 ⟨15, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83554404553443 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (225671507477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_16 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (41759893313349 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256719058633 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨16, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (41759893313349 / 50000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256719058633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_17 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (20871298281201 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256723085183 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨17, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (20871298281201 / 25000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256723085183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_18 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83450624013977 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (451345420263 / 20000000000000 : ℝ))
      (E := (cell12658 ⟨18, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83450624013977 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (451345420263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12658_19 : CellCertificate 12658 (887867628586519 / 10000000000000000 : ℝ) (829690773350067 / 500000000000000000 : ℝ) (167607042652961 / 5000000000000000 : ℝ)
    (cell12658 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · norm_num [cell12658]
  · have h := gap_lower (n := 12658) (a := (83416079260611 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256731111839 / 100000000000000 : ℝ))
      (E := (cell12658 ⟨19, by decide⟩).energy) (xi := (167607042652961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12658 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12658]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12658])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12658) (a := (83416079260611 / 100000000000000 : ℝ)) (b := (10170881657 / 6250000000000 : ℝ)) (q := (2256731111839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12658])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12658]

theorem cert12659_0 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (42038306363933 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564132728081 / 25000000000000 : ℝ))
      (E := (cell12659 ⟨0, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (42038306363933 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564132728081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_1 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (42020812286919 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564133721457 / 25000000000000 : ℝ))
      (E := (cell12659 ⟨1, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (42020812286919 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564133721457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_2 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (10500832671587 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256538911761 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨2, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (10500832671587 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256538911761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_3 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (83971723087897 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256542883393 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨3, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (83971723087897 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256542883393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_4 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (20984202420773 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256546867247 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨4, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (20984202420773 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256546867247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_5 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (2097548028053 / 2500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (28206885897 / 1250000000000 : ℝ))
      (E := (cell12659 ⟨5, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (2097548028053 / 2500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (28206885897 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_6 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (16773411473803 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256554905109 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨6, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (16773411473803 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256554905109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_7 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (16766443677599 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (28206985741 / 1250000000000 : ℝ))
      (E := (cell12659 ⟨7, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (16766443677599 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (28206985741 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_8 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (20949351035867 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225656285779 / 10000000000000 : ℝ))
      (E := (cell12659 ⟨8, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (20949351035867 / 25000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225656285779 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_9 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (8376261460003 / 10000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256566908053 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨9, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (8376261460003 / 10000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256566908053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_10 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41863924861229 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256570901157 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨10, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41863924861229 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256570901157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_11 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41846554737859 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256574901937 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨11, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41846554737859 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256574901937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_12 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41829196912477 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (282072357363 / 12500000000000 : ℝ))
      (E := (cell12659 ⟨12, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41829196912477 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (282072357363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_13 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (16724740547099 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128291447277 / 50000000000000 : ℝ))
      (E := (cell12659 ⟨13, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (16724740547099 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (1128291447277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_14 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (1671780723457 / 2000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256586898787 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨14, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (1671780723457 / 2000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256586898787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_15 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (16710878820541 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564147719347 / 25000000000000 : ℝ))
      (E := (cell12659 ⟨15, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (16710878820541 / 20000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (564147719347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_16 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (41759888245463 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256594894077 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨16, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (41759888245463 / 50000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256594894077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_17 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (83485183303557 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225659889601 / 10000000000000 : ℝ))
      (E := (cell12659 ⟨17, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (83485183303557 / 100000000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (225659889601 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_18 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (1303915851669 / 1562500000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256602888241 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨18, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (1303915851669 / 1562500000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256602888241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12659_19 : CellCertificate 12659 (110979939459681 / 1250000000000000 : ℝ) (1659250420315501 / 1000000000000000000 : ℝ) (335186954211609 / 10000000000000000 : ℝ)
    (cell12659 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · norm_num [cell12659]
  · have h := gap_lower (n := 12659) (a := (10427008758387 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256606875579 / 100000000000000 : ℝ))
      (E := (cell12659 ⟨19, by decide⟩).energy) (xi := (335186954211609 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12659 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12659]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12659])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12659) (a := (10427008758387 / 12500000000000 : ℝ)) (b := (162721093333 / 100000000000000 : ℝ)) (q := (2256606875579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12659])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12659]

theorem cert12660_0 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (84076597501513 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (70512709831 / 3125000000000 : ℝ))
      (E := (cell12660 ⟨0, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (84076597501513 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (70512709831 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_1 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (84041609669137 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564102677393 / 25000000000000 : ℝ))
      (E := (cell12660 ⟨1, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (84041609669137 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564102677393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_2 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (10500830848649 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128207349953 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨2, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (10500830848649 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128207349953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_3 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (5248231801571 / 6250000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (141026168409 / 6250000000000 : ℝ))
      (E := (cell12660 ⟨3, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (5248231801571 / 6250000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (141026168409 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_4 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (4196839787031 / 5000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256422702179 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨4, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (4196839787031 / 5000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256422702179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_5 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41950953749743 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256426731247 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨5, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41950953749743 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256426731247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_6 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41933522032883 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128215365989 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨6, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41933522032883 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128215365989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_7 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (83832205403683 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (70513584757 / 3125000000000 : ℝ))
      (E := (cell12660 ⟨7, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (83832205403683 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (70513584757 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_8 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (83797391477643 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256438737581 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨8, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (83797391477643 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256438737581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_9 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (20940650563061 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256442699427 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨9, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (20940650563061 / 25000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256442699427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_10 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (10465979711533 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (225644672087 / 10000000000000 : ℝ))
      (E := (cell12660 ⟨10, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (10465979711533 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (225644672087 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_11 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (83693097762669 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128225346347 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨11, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (83693097762669 / 100000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128225346347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_12 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (16731676485721 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1410284211 / 62500000000 : ℝ))
      (E := (cell12660 ⟨12, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (16731676485721 / 20000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1410284211 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_13 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41811845827701 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564114671917 / 25000000000000 : ℝ))
      (E := (cell12660 ⟨13, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41811845827701 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564114671917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_14 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (10448628176071 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128231361631 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨14, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (10448628176071 / 12500000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128231361631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_15 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (2611074489181 / 3125000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564116683497 / 25000000000000 : ℝ))
      (E := (cell12660 ⟨15, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (2611074489181 / 3125000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (564116683497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_16 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41759883178471 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128235362691 / 50000000000000 : ℝ))
      (E := (cell12660 ⟨16, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41759883178471 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (1128235362691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_17 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (4174258674203 / 5000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256474702739 / 100000000000000 : ℝ))
      (E := (cell12660 ⟨17, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (4174258674203 / 5000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (2256474702739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_18 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41725302500683 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (282059841167 / 12500000000000 : ℝ))
      (E := (cell12660 ⟨18, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41725302500683 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (282059841167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12660_19 : CellCertificate 12660 (55488212939627 / 625000000000000 : ℝ) (51847478582899 / 31250000000000000 : ℝ) (335159827573323 / 10000000000000000 : ℝ)
    (cell12660 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · norm_num [cell12660]
  · have h := gap_lower (n := 12660) (a := (41708030437627 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (45129653871 / 2000000000000 : ℝ))
      (E := (cell12660 ⟨19, by decide⟩).energy) (xi := (335159827573323 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12660 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12660]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12660])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12660) (a := (41708030437627 / 50000000000000 : ℝ)) (b := (162708082251 / 100000000000000 : ℝ)) (q := (45129653871 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12660])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12660]

theorem cert12661_0 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (84076582277569 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256282569893 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨0, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (84076582277569 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256282569893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_1 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16808318953361 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (451257317283 / 20000000000000 : ℝ))
      (E := (cell12661 ⟨1, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16808318953361 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (451257317283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_2 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (84006632208017 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256290599067 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨2, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (84006632208017 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256290599067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_3 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16794338912933 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256294558921 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨3, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16794338912933 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256294558921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_4 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (83936781800399 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256298590401 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨4, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (83936781800399 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256298590401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_5 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (10487736734883 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256302586163 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨5, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (10487736734883 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256302586163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_6 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (20966757691173 / 25000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128153277157 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨6, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (20966757691173 / 25000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128153277157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_7 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41916096210753 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256310560677 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨7, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41916096210753 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256310560677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_8 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41898689406957 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256314554927 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨8, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41898689406957 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256314554927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_9 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16752517981303 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282039825303 / 12500000000000 : ℝ))
      (E := (cell12661 ⟨9, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16752517981303 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (282039825303 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_10 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (10465978208011 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (564080648563 / 25000000000000 : ℝ))
      (E := (cell12661 ⟨10, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (10465978208011 / 12500000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (564080648563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_11 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (83693086051599 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256326595247 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨11, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (83693086051599 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256326595247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_12 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (83658371034197 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (451266110783 / 20000000000000 : ℝ))
      (E := (cell12661 ⟨12, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (83658371034197 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (451266110783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_13 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (8362368057721 / 10000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256334592753 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨13, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (8362368057721 / 10000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256334592753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_14 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (1671780292923 / 2000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128169300829 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨14, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (1671780292923 / 2000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128169300829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_15 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (41777186603353 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256342586413 / 100000000000000 : ℝ))
      (E := (cell12661 ⟨15, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (41777186603353 / 50000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (2256342586413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_16 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16703951244949 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128173276277 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨16, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16703951244949 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128173276277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_17 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (83485163666311 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128175281789 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨17, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (83485163666311 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128175281789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_18 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (83450595497627 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (18050836531 / 800000000000 : ℝ))
      (E := (cell12661 ⟨18, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (83450595497627 / 100000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (18050836531 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12661_19 : CellCertificate 12661 (110972912831907 / 1250000000000000 : ℝ) (829494114853511 / 500000000000000000 : ℝ) (167566352694933 / 5000000000000000 : ℝ)
    (cell12661 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · norm_num [cell12661]
  · have h := gap_lower (n := 12661) (a := (16683210337017 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128179282877 / 50000000000000 : ℝ))
      (E := (cell12661 ⟨19, by decide⟩).energy) (xi := (167566352694933 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12661 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12661]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12661])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12661) (a := (16683210337017 / 20000000000000 : ℝ)) (b := (10168442079 / 6250000000000 : ℝ)) (q := (1128179282877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12661])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12661]

theorem cert12662_0 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (2627392720501 / 3125000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256158478229 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨0, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (2627392720501 / 3125000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256158478229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_1 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (84041579866841 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564040629089 / 25000000000000 : ℝ))
      (E := (cell12662 ⟨1, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (84041579866841 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564040629089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_2 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (21001654407293 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451233298707 / 20000000000000 : ℝ))
      (E := (cell12662 ⟨2, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (21001654407293 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (451233298707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_3 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (20992920076621 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256170476523 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨3, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (20992920076621 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256170476523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_4 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (8393676786243 / 10000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (225617447401 / 10000000000000 : ℝ))
      (E := (cell12662 ⟨4, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (8393676786243 / 10000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (225617447401 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_5 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41950940130427 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (225617849443 / 10000000000000 : ℝ))
      (E := (cell12662 ⟨5, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41950940130427 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (225617849443 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_6 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83867017465791 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564045622003 / 25000000000000 : ℝ))
      (E := (cell12662 ⟨6, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83867017465791 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564045622003 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_7 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83832179441463 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256186462607 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨7, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83832179441463 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256186462607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_8 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83797366152281 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256190483807 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨8, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83797366152281 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256190483807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_9 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83762577562843 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256194501007 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨9, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83762577562843 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256194501007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_10 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (8372781363793 / 10000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256198463261 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨10, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (8372781363793 / 10000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256198463261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_11 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83693074342509 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128101246733 / 50000000000000 : ℝ))
      (E := (cell12662 ⟨11, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83693074342509 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128101246733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_12 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83658359641729 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (35253226283 / 1562500000000 : ℝ))
      (E := (cell12662 ⟨12, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83658359641729 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (35253226283 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_13 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83623669500921 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128105246791 / 50000000000000 : ℝ))
      (E := (cell12662 ⟨13, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83623669500921 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (1128105246791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_14 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (20897250971399 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256214475839 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨14, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (20897250971399 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256214475839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_15 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (20888590690361 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256218492821 / 100000000000000 : ℝ))
      (E := (cell12662 ⟨15, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (20888590690361 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (2256218492821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_16 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (41759873047167 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (141013905747 / 6250000000000 : ℝ))
      (E := (cell12662 ⟨16, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (41759873047167 / 50000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (141013905747 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_17 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83485153850311 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564056619631 / 25000000000000 : ℝ))
      (E := (cell12662 ⟨17, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83485153850311 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564056619631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_18 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (83450585995597 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564057628953 / 25000000000000 : ℝ))
      (E := (cell12662 ⟨18, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (83450585995597 / 100000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (564057628953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12662_19 : CellCertificate 12662 (8877552025401 / 100000000000000 : ℝ) (829428582736677 / 500000000000000000 : ℝ) (167552793830021 / 5000000000000000 : ℝ)
    (cell12662 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · norm_num [cell12662]
  · have h := gap_lower (n := 12662) (a := (20854010624147 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (70507327881 / 3125000000000 : ℝ))
      (E := (cell12662 ⟨19, by decide⟩).energy) (xi := (167552793830021 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12662 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12662]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12662])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12662) (a := (20854010624147 / 25000000000000 : ℝ)) (b := (81341033187 / 50000000000000 : ℝ)) (q := (70507327881 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12662])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12662]

theorem cert12663_0 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (42038275918451 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (5640086099 / 250000000000 : ℝ))
      (E := (cell12663 ⟨0, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (42038275918451 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (5640086099 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_1 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (42020782484623 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451207688313 / 20000000000000 : ℝ))
      (E := (cell12663 ⟨1, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (42020782484623 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451207688313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_2 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (5250412690791 / 6250000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451208488233 / 20000000000000 : ℝ))
      (E := (cell12663 ⟨2, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (5250412690791 / 6250000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (451208488233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_3 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (83971666050593 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256046447351 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨3, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (83971666050593 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256046447351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_4 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (10492094240839 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256050410909 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨4, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (10492094240839 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256050410909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_5 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (10487733330607 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256054456051 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨5, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (10487733330607 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256054456051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_6 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41933502084531 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256058417181 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨6, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41933502084531 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256058417181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_7 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41916083231777 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128031209009 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨7, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41916083231777 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128031209009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_8 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41898676746371 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128033204119 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨8, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41898676746371 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128033204119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_9 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41881282610613 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256070453199 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨9, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41881282610613 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256070453199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_10 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (83727801613789 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (112803722199 / 5000000000000 : ℝ))
      (E := (cell12663 ⟨10, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (83727801613789 / 100000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (112803722199 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_11 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41846531317699 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128039222709 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨11, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41846531317699 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128039222709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_12 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41829174125601 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256082406017 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨12, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41829174125601 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256082406017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_13 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41811829213267 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (225608644827 / 10000000000000 : ℝ))
      (E := (cell12663 ⟨13, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41811829213267 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (225608644827 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_14 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (16717798625381 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128045201971 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨14, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (16717798625381 / 20000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128045201971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_15 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (10444294039751 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (564023613303 / 25000000000000 : ℝ))
      (E := (cell12663 ⟨15, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (10444294039751 / 12500000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (564023613303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_16 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (8351973596571 / 10000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (141006151701 / 6250000000000 : ℝ))
      (E := (cell12663 ⟨16, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (8351973596571 / 10000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (141006151701 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_17 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (4174257201803 / 5000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256102447579 / 100000000000000 : ℝ))
      (E := (cell12663 ⟨17, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (4174257201803 / 5000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (2256102447579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_18 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41725288247639 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128053201483 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨18, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41725288247639 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128053201483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12663_19 : CellCertificate 12663 (887727106687549 / 10000000000000000 : ℝ) (331745224389371 / 200000000000000000 : ℝ) (5235601162229 / 156250000000000 : ℝ)
    (cell12663 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · norm_num [cell12663]
  · have h := gap_lower (n := 12663) (a := (41708016654881 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128055207307 / 50000000000000 : ℝ))
      (E := (cell12663 ⟨19, by decide⟩).energy) (xi := (5235601162229 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12663 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12663]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12663])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12663) (a := (41708016654881 / 50000000000000 : ℝ)) (b := (162669061579 / 100000000000000 : ℝ)) (q := (1128055207307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12663])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12663]

theorem cert12664_0 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (84076536620179 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1127955198101 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨0, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (84076536620179 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1127955198101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_1 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (42020775037009 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (18047315359 / 800000000000 : ℝ))
      (E := (cell12664 ⟨1, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (42020775037009 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (18047315359 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_2 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (21001647119617 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255918384107 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨2, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (21001647119617 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255918384107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_3 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83971651796991 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (225592241353 / 10000000000000 : ℝ))
      (E := (cell12664 ⟨3, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83971651796991 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (225592241353 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_4 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83936739993243 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (22559264011 / 1000000000000 : ℝ))
      (E := (cell12664 ⟨4, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83936739993243 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (22559264011 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_5 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83901853031069 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255930413103 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨5, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83901853031069 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255930413103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_6 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (16773398174901 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (281991799971 / 12500000000000 : ℝ))
      (E := (cell12664 ⟨6, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (16773398174901 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (281991799971 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_7 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41916076743889 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255938426911 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨7, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41916076743889 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255938426911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_8 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41898670417649 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255942386213 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨8, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41898670417649 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255942386213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_9 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41881276440833 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255946400979 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨9, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41881276440833 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255946400979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_10 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (16745557918333 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (225595042033 / 10000000000000 : ℝ))
      (E := (cell12664 ⟨10, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (16745557918333 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (225595042033 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_11 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (10461631366283 / 12500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255954393041 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨11, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (10461631366283 / 12500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255954393041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_12 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (41829168431307 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255958383719 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨12, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (41829168431307 / 50000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255958383719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_13 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (1306619489907 / 1562500000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255962398707 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨13, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (1306619489907 / 1562500000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255962398707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_14 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (83588982370077 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255966385967 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨14, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (83588982370077 / 100000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255966385967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_15 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (16710868375279 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255970409433 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨15, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (16710868375279 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255970409433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_16 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (10439965729859 / 12500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (140998401033 / 6250000000000 : ℝ))
      (E := (cell12664 ⟨16, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (10439965729859 / 12500000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (140998401033 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_17 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (16697026844711 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1127989206271 / 50000000000000 : ℝ))
      (E := (cell12664 ⟨17, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (16697026844711 / 20000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (1127989206271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_18 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (20862641749167 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255982402521 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨18, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (20862641749167 / 25000000000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255982402521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12664_19 : CellCertificate 12664 (887699015096587 / 10000000000000000 : ℝ) (1658595099122617 / 1000000000000000000 : ℝ) (335051365556511 / 10000000000000000 : ℝ)
    (cell12664 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · norm_num [cell12664]
  · have h := gap_lower (n := 12664) (a := (1303375376947 / 1562500000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255986391271 / 100000000000000 : ℝ))
      (E := (cell12664 ⟨19, by decide⟩).energy) (xi := (335051365556511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12664 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12664]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12664])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12664) (a := (1303375376947 / 1562500000000 : ℝ)) (b := (162656058879 / 100000000000000 : ℝ)) (q := (2255986391271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12664])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12664]

theorem cert12665_0 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (42038260702931 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255786405843 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨0, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (42038260702931 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255786405843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_1 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (84041535181157 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281973806411 / 12500000000000 : ℝ))
      (E := (cell12665 ⟨1, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (84041535181157 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281973806411 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_2 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (5250410869163 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563948609517 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨2, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (5250410869163 / 6250000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563948609517 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_3 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41985818772839 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127899216469 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨3, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41985818772839 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127899216469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_4 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (10492090757753 / 12500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255802444583 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨4, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (10492090757753 / 12500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255802444583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_5 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (20975459854873 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281975802939 / 12500000000000 : ℝ))
      (E := (cell12665 ⟨5, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (20975459854873 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281975802939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_6 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (2096674439553 / 2500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127905217887 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨6, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (2096674439553 / 2500000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127905217887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_7 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41916070257067 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255814431317 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨7, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41916070257067 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255814431317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_8 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (20949332044987 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127909208867 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨8, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (20949332044987 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127909208867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_9 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (523515878401 / 625000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (225582240237 / 10000000000000 : ℝ))
      (E := (cell12665 ⟨9, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (523515878401 / 625000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (225582240237 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_10 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41863888785779 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255826392311 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨10, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41863888785779 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255826392311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_11 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83693039227109 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127915197199 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨11, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83693039227109 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127915197199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_12 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41829162737983 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (112791720761 / 5000000000000 : ℝ))
      (E := (cell12665 ⟨12, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41829162737983 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (112791720761 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_13 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41811818141731 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127919201503 / 50000000000000 : ℝ))
      (E := (cell12665 ⟨13, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41811818141731 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (1127919201503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_14 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83588971615111 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563960605479 / 25000000000000 : ℝ))
      (E := (cell12665 ⟨14, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83588971615111 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (563960605479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_15 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41777165718303 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (56396160491 / 2500000000000 : ℝ))
      (E := (cell12665 ⟨15, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41777165718303 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (56396160491 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_16 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83519715713819 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255850401709 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨16, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83519715713819 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255850401709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_17 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (41742562206399 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255854431617 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨17, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (41742562206399 / 50000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255854431617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_18 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (83450557499767 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281982299753 / 12500000000000 : ℝ))
      (E := (cell12665 ⟨18, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (83450557499767 / 100000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (281982299753 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12665_19 : CellCertificate 12665 (221917731941549 / 2500000000000000 : ℝ) (1658464096995737 / 1000000000000000000 : ℝ) (167512130590207 / 5000000000000000 : ℝ)
    (cell12665 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · norm_num [cell12665]
  · have h := gap_lower (n := 12665) (a := (20854003735281 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255862422167 / 100000000000000 : ℝ))
      (E := (cell12665 ⟨19, by decide⟩).energy) (xi := (167512130590207 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12665 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12665]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12665])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12665) (a := (20854003735281 / 25000000000000 : ℝ)) (b := (162643058273 / 100000000000000 : ℝ)) (q := (2255862422167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12665])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12665]

theorem cert12666_0 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (84076506193951 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255662468523 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨0, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (84076506193951 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255662468523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_1 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (42020760145331 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127833238987 / 50000000000000 : ℝ))
      (E := (cell12666 ⟨1, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (42020760145331 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127833238987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_2 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (42003279668537 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (140979405459 / 6250000000000 : ℝ))
      (E := (cell12666 ⟨2, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (42003279668537 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (140979405459 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_3 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83971623296653 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255674447699 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨3, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83971623296653 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255674447699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_4 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (41968356066527 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (112783924173 / 5000000000000 : ℝ))
      (E := (cell12666 ⟨4, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (41968356066527 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (112783924173 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_5 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (41950912905063 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255682487277 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨5, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (41950912905063 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255682487277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_6 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83866964291907 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563921616813 / 25000000000000 : ℝ))
      (E := (cell12666 ⟨6, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83866964291907 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563921616813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_7 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83832127542623 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (451138097841 / 20000000000000 : ℝ))
      (E := (cell12666 ⟨7, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83832127542623 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (451138097841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_8 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83797315526691 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255694444809 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨8, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83797315526691 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255694444809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_9 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (8376252820871 / 10000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225569845737 / 10000000000000 : ℝ))
      (E := (cell12666 ⟨9, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (8376252820871 / 10000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (225569845737 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_10 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (41863882776733 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255702476007 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨10, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (41863882776733 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255702476007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_11 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83693027525931 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563926612373 / 25000000000000 : ℝ))
      (E := (cell12666 ⟨11, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83693027525931 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (563926612373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_12 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (10457289261407 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (56392762513 / 2500000000000 : ℝ))
      (E := (cell12666 ⟨12, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (10457289261407 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (56392762513 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_13 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83623625214777 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255714461167 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨13, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83623625214777 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255714461167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_14 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83588960862007 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (281964806707 / 12500000000000 : ℝ))
      (E := (cell12666 ⟨14, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83588960862007 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (281964806707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_15 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83554320998641 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127861241917 / 50000000000000 : ℝ))
      (E := (cell12666 ⟨15, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83554320998641 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127861241917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_16 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (10439963198819 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255726499121 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨16, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (10439963198819 / 12500000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255726499121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_17 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (20871278650947 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (11278652233 / 500000000000 : ℝ))
      (E := (cell12666 ⟨17, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (20871278650947 / 25000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (11278652233 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_18 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (41725274002287 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127867223851 / 50000000000000 : ℝ))
      (E := (cell12666 ⟨18, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (41725274002287 / 50000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (1127867223851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12666_19 : CellCertificate 12666 (887642844695361 / 10000000000000000 : ℝ) (414583278890327 / 250000000000000000 : ℝ) (33499716125317 / 1000000000000000 : ℝ)
    (cell12666 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · norm_num [cell12666]
  · have h := gap_lower (n := 12666) (a := (83416005759311 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255738449049 / 100000000000000 : ℝ))
      (E := (cell12666 ⟨19, by decide⟩).energy) (xi := (33499716125317 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12666 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12666]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12666])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12666) (a := (83416005759311 / 100000000000000 : ℝ)) (b := (162630059761 / 100000000000000 : ℝ)) (q := (2255738449049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12666])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12666]

theorem cert12667_0 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (16815298196889 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563884646061 / 25000000000000 : ℝ))
      (E := (cell12667 ⟨0, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (16815298196889 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563884646061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_1 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (84041505402533 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563885639441 / 25000000000000 : ℝ))
      (E := (cell12667 ⟨1, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (84041505402533 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563885639441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_2 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (21001636192467 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127773294893 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨2, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (21001636192467 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127773294893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_3 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (16794321809983 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (225555057357 / 10000000000000 : ℝ))
      (E := (cell12667 ⟨3, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (16794321809983 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (225555057357 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_4 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20984174551583 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255554575633 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨4, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20984174551583 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255554575633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_5 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83901812202969 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255558546477 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨5, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83901812202969 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255558546477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_6 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83866951003863 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127781276077 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨6, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83866951003863 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127781276077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_7 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20958028643311 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (140972908913 / 6250000000000 : ℝ))
      (E := (cell12667 ⟨7, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20958028643311 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (140972908913 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_8 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83797302875527 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127785291713 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨8, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83797302875527 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127785291713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_9 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83762515875313 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255574565983 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨9, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83762515875313 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255574565983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_10 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83727753537391 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (451115711067 / 20000000000000 : ℝ))
      (E := (cell12667 ⟨10, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83727753537391 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (451115711067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_11 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (8369301582673 / 10000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255582558323 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨11, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (8369301582673 / 10000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255582558323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_12 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (16731660541697 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563896645383 / 25000000000000 : ℝ))
      (E := (cell12667 ⟨12, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (16731660541697 / 20000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (563896645383 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_13 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83623614147991 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (281948821649 / 12500000000000 : ℝ))
      (E := (cell12667 ⟨13, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83623614147991 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (281948821649 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_14 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20897237527691 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255594539323 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨14, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20897237527691 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255594539323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_15 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83554310562499 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (112779927193 / 5000000000000 : ℝ))
      (E := (cell12667 ⟨15, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83554310562499 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (112779927193 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_16 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83519695469069 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255602534223 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨16, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83519695469069 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255602534223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_17 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (20871276199131 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255606573903 / 100000000000000 : ℝ))
      (E := (cell12667 ⟨17, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (20871276199131 / 25000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (2255606573903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_18 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (8345053851109 / 10000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127805275779 / 50000000000000 : ℝ))
      (E := (cell12667 ⟨18, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (8345053851109 / 10000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (1127805275779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12667_19 : CellCertificate 12667 (887614765883067 / 10000000000000000 : ℝ) (165820215481443 / 100000000000000000 : ℝ) (167485032886793 / 5000000000000000 : ℝ)
    (cell12667 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · norm_num [cell12667]
  · have h := gap_lower (n := 12667) (a := (83415996579167 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (281951823553 / 12500000000000 : ℝ))
      (E := (cell12667 ⟨19, by decide⟩).energy) (xi := (167485032886793 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12667 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12667]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12667])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12667) (a := (83415996579167 / 100000000000000 : ℝ)) (b := (81308531671 / 50000000000000 : ℝ)) (q := (281951823553 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12667])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12667]

theorem cert12668_0 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (42038237888671 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255414695203 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨0, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (42038237888671 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255414695203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_1 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (84041490516769 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127709345331 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨1, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (84041490516769 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127709345331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_2 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (84006530204987 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127711343773 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨2, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (84006530204987 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127711343773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_3 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (10496449350683 / 12500000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127713347399 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨3, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (10496449350683 / 12500000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127713347399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_4 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41968342140929 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127715331601 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨4, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41968342140929 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127715331601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_5 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (4195089929901 / 5000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255434659039 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨5, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (4195089929901 / 5000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255434659039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_6 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (8386693771799 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (28192983631 / 1250000000000 : ℝ))
      (E := (cell12668 ⟨6, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (8386693771799 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (28192983631 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_7 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (20958025401499 / 25000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (225544270747 / 10000000000000 : ℝ))
      (E := (cell12668 ⟨7, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (20958025401499 / 25000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (225544270747 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_8 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (16759458045291 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (451089331921 / 20000000000000 : ℝ))
      (E := (cell12668 ⟨8, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (16759458045291 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (451089331921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_9 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (8376250354397 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255450670191 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨9, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (8376250354397 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255450670191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_10 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83727741523329 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127727344171 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨10, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83727741523329 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127727344171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_11 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (16738600825901 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (225545866283 / 10000000000000 : ℝ))
      (E := (cell12668 ⟨11, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (16738600825901 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (225545866283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_12 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83658291327651 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255462658261 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨12, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83658291327651 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255462658261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_13 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (2613237596347 / 3125000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255466680971 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨13, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (2613237596347 / 3125000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255466680971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_14 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (41794469680691 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127735339459 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨14, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (41794469680691 / 50000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127735339459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_15 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83554300128179 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255474657877 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨15, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83554300128179 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255474657877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_16 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (8351968534937 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (56386967039 / 2500000000000 : ℝ))
      (E := (cell12668 ⟨16, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (8351968534937 / 10000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (56386967039 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_17 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (16697018998201 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127741348559 / 50000000000000 : ℝ))
      (E := (cell12668 ⟨17, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (16697018998201 / 20000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (1127741348559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_18 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83450529019313 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255486709593 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨18, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83450529019313 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255486709593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12668_19 : CellCertificate 12668 (443793345664149 / 5000000000000000 : ℝ) (829035607375101 / 500000000000000000 : ℝ) (334942974740469 / 10000000000000000 : ℝ)
    (cell12668 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · norm_num [cell12668]
  · have h := gap_lower (n := 12668) (a := (83415987400693 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255490665537 / 100000000000000 : ℝ))
      (E := (cell12668 ⟨19, by decide⟩).energy) (xi := (334942974740469 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12668 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12668]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12668])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12668) (a := (83415987400693 / 100000000000000 : ℝ)) (b := (32520813803 / 20000000000000 : ℝ)) (q := (2255490665537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12668])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12668]

theorem cert12669_0 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (21019115143161 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255290859203 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨0, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (21019115143161 / 25000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255290859203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_1 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (84041475633369 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255294876667 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨1, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (84041475633369 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255294876667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_2 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (1312601806913 / 1562500000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563824709619 / 25000000000000 : ℝ))
      (E := (cell12669 ⟨2, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (1312601806913 / 1562500000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563824709619 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_3 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (839715805633 / 1000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255302869259 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨3, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (839715805633 / 1000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255302869259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_4 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (5246041897477 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255306861969 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨4, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (5246041897477 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255306861969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_5 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83901784995281 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (880980791 / 39062500000 : ℝ))
      (E := (cell12669 ⟨5, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83901784995281 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (880980791 / 39062500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_6 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41933462217143 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127657412141 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨6, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41933462217143 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127657412141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_7 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41916044320439 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (281914858481 / 12500000000000 : ℝ))
      (E := (cell12669 ⟨7, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41916044320439 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (281914858481 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_8 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (3351891103179 / 4000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255322847329 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨8, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (3351891103179 / 4000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255322847329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_9 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (2094062280367 / 2500000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255326828013 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨9, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (2094062280367 / 2500000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255326828013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_10 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83727729511283 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255330816983 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨10, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83727729511283 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255330816983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_11 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (5230812027141 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563833705269 / 25000000000000 : ℝ))
      (E := (cell12669 ⟨11, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (5230812027141 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (563833705269 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_12 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (16731655989751 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127669423439 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨12, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (16731655989751 / 20000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127669423439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_13 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83623592020117 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (451068568523 / 20000000000000 : ℝ))
      (E := (cell12669 ⟨13, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83623592020117 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (451068568523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_14 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (4179446430693 / 5000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127673436221 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨14, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (4179446430693 / 5000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127673436221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_15 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83554289695681 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127675412943 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨15, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83554289695681 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127675412943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_16 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (41759837615727 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225535482477 / 10000000000000 : ℝ))
      (E := (cell12669 ⟨16, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (41759837615727 / 50000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (225535482477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_17 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (2608908912101 / 3125000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255358874449 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨17, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (2608908912101 / 3125000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255358874449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_18 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (83450519529243 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255362863579 / 100000000000000 : ℝ))
      (E := (cell12669 ⟨18, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (83450519529243 / 100000000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (2255362863579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12669_19 : CellCertificate 12669 (887558621030039 / 10000000000000000 : ℝ) (414485073840931 / 250000000000000000 : ℝ) (167457944076313 / 5000000000000000 : ℝ)
    (cell12669 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · norm_num [cell12669]
  · have h := gap_lower (n := 12669) (a := (5213498638993 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127683427571 / 50000000000000 : ℝ))
      (E := (cell12669 ⟨19, by decide⟩).energy) (xi := (167457944076313 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12669 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12669]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12669])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12669) (a := (5213498638993 / 6250000000000 : ℝ)) (b := (162591076781 / 100000000000000 : ℝ)) (q := (1127683427571 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12669])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12669]

theorem cert12670_0 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (84076445370349 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255167018443 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨0, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (84076445370349 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255167018443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_1 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (42020730376167 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255171057949 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨1, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (42020730376167 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255171057949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_2 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (84006501082201 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (112758752129 / 5000000000000 : ℝ))
      (E := (cell12670 ⟨2, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (84006501082201 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (112758752129 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_3 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83971566323421 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (56379475977 / 2500000000000 : ℝ))
      (E := (cell12670 ⟨3, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83971566323421 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (56379475977 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_4 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83936656439653 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127591528067 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨4, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83936656439653 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127591528067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_5 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83901771394749 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451037408849 / 20000000000000 : ℝ))
      (E := (cell12670 ⟨5, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83901771394749 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451037408849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_6 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83866911152751 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127595534729 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨6, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83866911152751 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127595534729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_7 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83832075677891 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (17618711123 / 781250000000 : ℝ))
      (E := (cell12670 ⟨7, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83832075677891 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (17618711123 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_8 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83797264934587 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255199030611 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨8, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83797264934587 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255199030611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_9 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (83762478887443 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255203039451 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨9, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (83762478887443 / 100000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255203039451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_10 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (66982174001 / 80000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451041411469 / 20000000000000 : ℝ))
      (E := (cell12670 ⟨10, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (66982174001 / 80000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451041411469 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_11 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41846490370491 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451042206613 / 20000000000000 : ℝ))
      (E := (cell12670 ⟨11, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41846490370491 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (451042206613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_12 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (16731653714359 / 20000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127607515607 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨12, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (16731653714359 / 20000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127607515607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_13 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (20905895239757 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255219058127 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨13, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (20905895239757 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255219058127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_14 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41794458934099 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255223061761 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨14, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41794458934099 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255223061761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_15 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (20888569816251 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (140951690493 / 6250000000000 : ℝ))
      (E := (cell12670 ⟨15, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (20888569816251 / 25000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (140951690493 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_16 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (41759832557661 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563807755509 / 25000000000000 : ℝ))
      (E := (cell12670 ⟨16, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (41759832557661 / 50000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (563807755509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_17 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (16697015077041 / 20000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255235047693 / 100000000000000 : ℝ))
      (E := (cell12670 ⟨17, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (16697015077041 / 20000000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (2255235047693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_18 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (1043131375511 / 1250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127619535873 / 50000000000000 : ℝ))
      (E := (cell12670 ⟨18, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (1043131375511 / 1250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (1127619535873 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12670_19 : CellCertificate 12670 (887530554987277 / 10000000000000000 : ℝ) (1657809396650099 / 1000000000000000000 : ℝ) (10465275187777 / 312500000000000 : ℝ)
    (cell12670 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · norm_num [cell12670]
  · have h := gap_lower (n := 12670) (a := (5213498065547 / 6250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (112762152037 / 5000000000000 : ℝ))
      (E := (cell12670 ⟨19, by decide⟩).energy) (xi := (10465275187777 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12670 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12670]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12670])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12670) (a := (5213498065547 / 6250000000000 : ℝ)) (b := (81289043319 / 50000000000000 : ℝ)) (q := (112762152037 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12670])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12670]

theorem cert12671_0 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (84076430170457 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451008657707 / 20000000000000 : ℝ))
      (E := (cell12671 ⟨0, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (84076430170457 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451008657707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_1 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (42020722936831 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127523646171 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨1, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (42020722936831 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127523646171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_2 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (10500810815537 / 12500000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127525649927 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨2, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (10500810815537 / 12500000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127525649927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_3 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (20992888021457 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (281881907767 / 12500000000000 : ℝ))
      (E := (cell12671 ⟨3, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (20992888021457 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (281881907767 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_4 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83936642521919 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255059303601 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨4, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83936642521919 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255059303601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_5 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (10487719724553 / 12500000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255063258969 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨5, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (10487719724553 / 12500000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255063258969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_6 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (16773379574677 / 20000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563766813041 / 25000000000000 : ℝ))
      (E := (cell12671 ⟨6, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (16773379574677 / 20000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563766813041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_7 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83832062717033 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255071291101 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨7, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83832062717033 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255071291101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_8 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83797252291789 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255075267447 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨8, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83797252291789 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255075267447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_9 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (41881233281129 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127539623243 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨9, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (41881233281129 / 50000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127539623243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_10 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83727705493231 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451016658669 / 20000000000000 : ℝ))
      (E := (cell12671 ⟨10, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83727705493231 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (451016658669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_11 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83692969049683 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563771824699 / 25000000000000 : ℝ))
      (E := (cell12671 ⟨11, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83692969049683 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563771824699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_12 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (20914564299193 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127545634677 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨12, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (20914564299193 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127545634677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_13 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (20905892474959 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563773817349 / 25000000000000 : ℝ))
      (E := (cell12671 ⟨13, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (20905892474959 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563773817349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_14 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (20897226781099 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563774811719 / 25000000000000 : ℝ))
      (E := (cell12671 ⟨14, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (20897226781099 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563774811719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_15 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83554268836149 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563775816431 / 25000000000000 : ℝ))
      (E := (cell12671 ⟨15, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83554268836149 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (563775816431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_16 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83519655000973 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255107273357 / 100000000000000 : ℝ))
      (E := (cell12671 ⟨16, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83519655000973 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (2255107273357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_17 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83485065584921 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127555637529 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨17, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83485065584921 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127555637529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_18 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (83450500554223 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127557637933 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨18, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (83450500554223 / 100000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127557637933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12671_19 : CellCertificate 12671 (887502493198997 / 10000000000000000 : ℝ) (165767851860443 / 100000000000000000 : ℝ) (167430864153997 / 5000000000000000 : ℝ)
    (cell12671 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · norm_num [cell12671]
  · have h := gap_lower (n := 12671) (a := (20853989968821 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127559640291 / 50000000000000 : ℝ))
      (E := (cell12671 ⟨19, by decide⟩).energy) (xi := (167430864153997 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12671 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12671]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12671])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12671) (a := (20853989968821 / 25000000000000 : ℝ)) (b := (162565098587 / 100000000000000 : ℝ)) (q := (1127559640291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12671])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12671]

theorem cert12672_0 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (42038207486483 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254919553869 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨0, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (42038207486483 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254919553869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_1 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (84041430997353 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (450984704403 / 20000000000000 : ℝ))
      (E := (cell12672 ⟨1, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (84041430997353 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (450984704403 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_2 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (84006471968713 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563731888113 / 25000000000000 : ℝ))
      (E := (cell12672 ⟨2, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (84006471968713 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563731888113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_3 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83971537850519 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (4404163161 / 195312500000 : ℝ))
      (E := (cell12672 ⟨3, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83971537850519 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (4404163161 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_4 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (2623019643951 / 3125000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563733886617 / 25000000000000 : ℝ))
      (E := (cell12672 ⟨4, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (2623019643951 / 3125000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (563733886617 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_5 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41950872100153 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254939527059 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨5, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41950872100153 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254939527059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_6 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41933442298093 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254943546249 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨6, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41933442298093 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254943546249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_7 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (16766409951661 / 20000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254947553979 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨7, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (16766409951661 / 20000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254947553979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_8 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41898619825541 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254951557837 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨8, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41898619825541 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254951557837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_9 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (670099633913 / 800000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127477782579 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨9, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (670099633913 / 800000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127477782579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_10 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (3349107739489 / 4000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (281869940623 / 12500000000000 : ℝ))
      (E := (cell12672 ⟨10, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (3349107739489 / 4000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (281869940623 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_11 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83692957360359 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127481780103 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨11, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83692957360359 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127481780103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_12 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (16731649164737 / 20000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254967561301 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨12, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (16731649164737 / 20000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254967561301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_13 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41811779421271 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (450994306907 / 20000000000000 : ℝ))
      (E := (cell12672 ⟨13, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41811779421271 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (450994306907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_14 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (20897224095613 / 25000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254975544059 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨14, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (20897224095613 / 25000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254975544059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_15 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41777129204557 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254979537557 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨15, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41777129204557 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254979537557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_16 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41759822444203 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (450996704111 / 20000000000000 : ℝ))
      (E := (cell12672 ⟨16, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41759822444203 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (450996704111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_17 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (41742527893191 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127493778271 / 50000000000000 : ℝ))
      (E := (cell12672 ⟨17, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (41742527893191 / 50000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (1127493778271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_18 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83450491069273 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254991534169 / 100000000000000 : ℝ))
      (E := (cell12672 ⟨18, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83450491069273 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (2254991534169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12672_19 : CellCertificate 12672 (110934304458023 / 1250000000000000 : ℝ) (1657547661221823 / 1000000000000000000 : ℝ) (41854331881103 / 1250000000000000 : ℝ)
    (cell12672 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · norm_num [cell12672]
  · have h := gap_lower (n := 12672) (a := (83415950703483 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (225499557467 / 10000000000000 : ℝ))
      (E := (cell12672 ⟨19, by decide⟩).energy) (xi := (41854331881103 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12672 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12672]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12672])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12672) (a := (83415950703483 / 100000000000000 : ℝ)) (b := (81276056313 / 50000000000000 : ℝ)) (q := (225499557467 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12672])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12672]

theorem cert12673_0 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (42038199888939 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563698968063 / 25000000000000 : ℝ))
      (E := (cell12673 ⟨0, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (42038199888939 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563698968063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_1 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (42020708061703 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127399931317 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨1, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (42020708061703 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127399931317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_2 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (16801291483091 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127401929113 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨2, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (16801291483091 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127401929113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_3 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41985761808747 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254807867969 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨3, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41985761808747 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254807867969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_4 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83936614693189 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (28185148033 / 1250000000000 : ℝ))
      (E := (cell12673 ⟨4, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83936614693189 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (28185148033 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_5 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (16780346121279 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450963169703 / 20000000000000 : ℝ))
      (E := (cell12673 ⟨5, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (16780346121279 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450963169703 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_6 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (16773374264231 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450963967163 / 20000000000000 : ℝ))
      (E := (cell12673 ⟨6, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (16773374264231 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450963967163 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_7 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (10479004600213 / 12500000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (140926491897 / 6250000000000 : ℝ))
      (E := (cell12673 ⟨7, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (10479004600213 / 12500000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (140926491897 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_8 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (5237326688279 / 6250000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254827843791 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨8, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (5237326688279 / 6250000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254827843791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_9 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83762441918043 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127415910707 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨9, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83762441918043 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127415910707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_10 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (2616490046351 / 3125000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563708967087 / 25000000000000 : ℝ))
      (E := (cell12673 ⟨10, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (2616490046351 / 3125000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (563708967087 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_11 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83692945673009 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127419937681 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨11, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83692945673009 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127419937681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_12 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83658234452533 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (225484384897 / 10000000000000 : ℝ))
      (E := (cell12673 ⟨12, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83658234452533 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (225484384897 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_13 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (16724709557429 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127423926773 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨13, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (16724709557429 / 20000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127423926773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_14 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (653038169081 / 781250000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254851837041 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨14, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (653038169081 / 781250000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254851837041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_15 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (835542479839 / 1000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254855863387 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨15, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (835542479839 / 1000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254855863387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_16 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83519634777621 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127429910907 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨16, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83519634777621 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127429910907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_17 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (41742522994793 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450972766789 / 20000000000000 : ℝ))
      (E := (cell12673 ⟨17, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (41742522994793 / 50000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (450972766789 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_18 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (83450481586027 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254867846659 / 100000000000000 : ℝ))
      (E := (cell12673 ⟨18, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (83450481586027 / 100000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (2254867846659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12673_19 : CellCertificate 12673 (443723191190913 / 5000000000000000 : ℝ) (207177103062173 / 125000000000000000 : ℝ) (334807586230163 / 10000000000000000 : ℝ)
    (cell12673 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · norm_num [cell12673]
  · have h := gap_lower (n := 12673) (a := (1668318830667 / 2000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127435932377 / 50000000000000 : ℝ))
      (E := (cell12673 ⟨19, by decide⟩).energy) (xi := (334807586230163 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12673 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12673]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12673])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12673) (a := (1668318830667 / 2000000000000 : ℝ)) (b := (81269564377 / 50000000000000 : ℝ)) (q := (1127435932377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12673])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12673]

theorem cert12674_0 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (8407638458519 / 10000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254672185877 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨0, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (8407638458519 / 10000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254672185877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_1 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (84041401251821 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127338099267 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨1, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (84041401251821 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127338099267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_2 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (42003221432259 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254680217177 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨2, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (42003221432259 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254680217177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_3 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (41985754693377 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127342096433 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨3, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (41985754693377 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127342096433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_4 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (5246037548887 / 6250000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254688192113 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨4, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (5246037548887 / 6250000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254688192113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_5 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83901717014689 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127346082707 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨5, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83901717014689 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127346082707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_6 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83866858048291 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254696178811 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨6, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83866858048291 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254696178811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_7 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (1309875372613 / 1562500000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450940036449 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨7, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (1309875372613 / 1562500000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450940036449 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_8 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (20458304291 / 24414062500 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (22547041833 / 1000000000000 : ℝ))
      (E := (cell12674 ⟨8, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (20458304291 / 24414062500 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (22547041833 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_9 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83762429599011 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563677047327 / 25000000000000 : ℝ))
      (E := (cell12674 ⟨9, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83762429599011 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563677047327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_10 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (13396427117 / 16000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254712207353 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨10, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (13396427117 / 16000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254712207353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_11 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (5230808374227 / 6250000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254716186199 / 100000000000000 : ℝ))
      (E := (cell12674 ⟨11, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (5230808374227 / 6250000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (2254716186199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_12 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (20914555770829 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127360095223 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨12, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (20914555770829 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127360095223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_13 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (16724707346729 / 20000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450944833663 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨13, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (16724707346729 / 20000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450944833663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_14 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83588874904141 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127364091979 / 50000000000000 : ℝ))
      (E := (cell12674 ⟨14, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83588874904141 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (1127364091979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_15 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (16710847512101 / 20000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (70460380783 / 3125000000000 : ℝ))
      (E := (cell12674 ⟨15, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (16710847512101 / 20000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (70460380783 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_16 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83519624668617 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563684044283 / 25000000000000 : ℝ))
      (E := (cell12674 ⟨16, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83519624668617 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563684044283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_17 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (41742518097267 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563685041367 / 25000000000000 : ℝ))
      (E := (cell12674 ⟨17, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (41742518097267 / 50000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563685041367 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_18 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (83450472104487 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563686053333 / 25000000000000 : ℝ))
      (E := (cell12674 ⟨18, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (83450472104487 / 100000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (563686053333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

theorem cert12674_19 : CellCertificate 12674 (88741833335091 / 1000000000000000 : ℝ) (103580375526639 / 62500000000000000 : ℝ) (167390260925411 / 5000000000000000 : ℝ)
    (cell12674 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · norm_num [cell12674]
  · have h := gap_lower (n := 12674) (a := (20853983091221 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450949641817 / 20000000000000 : ℝ))
      (E := (cell12674 ⟨19, by decide⟩).energy) (xi := (167390260925411 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12674 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12674]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12674])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12674) (a := (20853983091221 / 25000000000000 : ℝ)) (b := (162526146973 / 100000000000000 : ℝ)) (q := (450949641817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12674])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12674]

end BstLean.Part268
