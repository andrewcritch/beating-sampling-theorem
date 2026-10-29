import BstLean.Part268CellShard28Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13050_0 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (84070837369151 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210319399131 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨0, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (84070837369151 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210319399131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_1 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (42017974111393 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (55258085491 / 2500000000000 : ℝ))
      (E := (cell13050 ⟨1, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (42017974111393 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (55258085491 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_2 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41016154243 / 48828125000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105163719659 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨2, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41016154243 / 48828125000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105163719659 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_3 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (1679324886671 / 2000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (221033140863 / 10000000000000 : ℝ))
      (E := (cell13050 ⟨3, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (1679324886671 / 2000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (221033140863 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_4 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41965714759201 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210335451499 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨4, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41965714759201 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210335451499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_5 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (20974159852091 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210339459937 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨5, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (20974159852091 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210339459937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_6 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83861873967771 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105171720741 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨6, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83861873967771 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105171720741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_7 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (10478391645143 / 12500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552586865357 / 25000000000000 : ℝ))
      (E := (cell13050 ⟨7, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (10478391645143 / 12500000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (552586865357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_8 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83792416953187 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210351468849 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨8, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83792416953187 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210351468849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_9 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83757725308793 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (88414218821 / 4000000000000 : ℝ))
      (E := (cell13050 ⟨9, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83757725308793 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (88414218821 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_10 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83723058193033 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210359472991 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨10, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83723058193033 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210359472991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_11 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (20922103892791 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210363482531 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨11, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (20922103892791 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210363482531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_12 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41826898704311 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210367505181 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨12, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41826898704311 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210367505181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_13 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83619203671023 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105185744291 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨13, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83619203671023 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105185744291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_14 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41792317162081 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210375496381 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨14, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41792317162081 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210375496381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_15 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (8355008933401 / 10000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105189766939 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨15, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (8355008933401 / 10000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105189766939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_16 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (41757784333357 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105191773957 / 50000000000000 : ℝ))
      (E := (cell13050 ⟨16, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (41757784333357 / 50000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (1105191773957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_17 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (83481072288599 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210387543231 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨17, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (83481072288599 / 100000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210387543231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_18 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (1043082502077 / 1250000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (11051957913 / 500000000000 : ℝ))
      (E := (cell13050 ⟨18, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (1043082502077 / 1250000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (11051957913 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13050_19 : CellCertificate 13050 (877164443330237 / 10000000000000000 : ℝ) (402380143360563 / 250000000000000000 : ℝ) (64981752917651 / 2000000000000000 : ℝ)
    (cell13050 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · norm_num [cell13050]
  · have h := gap_lower (n := 13050) (a := (20853038066517 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210395553777 / 100000000000000 : ℝ))
      (E := (cell13050 ⟨19, by decide⟩).energy) (xi := (64981752917651 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13050 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13050]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13050])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13050) (a := (20853038066517 / 25000000000000 : ℝ)) (b := (9861783747 / 6250000000000 : ℝ)) (q := (2210395553777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13050])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13050]

theorem cert13051_0 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (84070823042627 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210206319343 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨0, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (84070823042627 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210206319343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_1 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (42017966951311 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105105167491 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨1, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (42017966951311 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105105167491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_2 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (42000534787927 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210214291947 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨2, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (42000534787927 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210214291947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_3 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83966230026089 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105109157187 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨3, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83966230026089 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105109157187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_4 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (20982853804321 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105111176257 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨4, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (20982853804321 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105111176257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_5 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (5243539069599 / 6250000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210226356269 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨5, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (5243539069599 / 6250000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210226356269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_6 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41930929839661 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (110511516659 / 5000000000000 : ℝ))
      (E := (cell13051 ⟨6, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41930929839661 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (110511516659 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_7 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83827118879021 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105117174269 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨7, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83827118879021 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105117174269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_8 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (10474050334673 / 12500000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210238351419 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨8, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (10474050334673 / 12500000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210238351419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_9 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (10469713879913 / 12500000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210242348601 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨9, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (10469713879913 / 12500000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210242348601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_10 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41861521964927 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105123202349 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨10, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41861521964927 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105123202349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_11 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (5230525082143 / 6250000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210250409861 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨11, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (5230525082143 / 6250000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210250409861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_12 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (20913445789511 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (110512721409 / 5000000000000 : ℝ))
      (E := (cell13051 ⟨12, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (20913445789511 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (110512721409 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_13 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41809594713369 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105129203649 / 50000000000000 : ℝ))
      (E := (cell13051 ⟨13, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41809594713369 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (1105129203649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_14 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83584620086163 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210262410861 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨14, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83584620086163 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210262410861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_15 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (20887518775573 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210266444169 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨15, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (20887518775573 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210266444169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_16 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (83515554441273 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (110513522703 / 5000000000000 : ℝ))
      (E := (cell13051 ⟨16, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (83515554441273 / 100000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (110513522703 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_17 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (20870264517357 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210274445281 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨17, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (20870264517357 / 25000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210274445281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_18 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41723292976627 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (11051392403 / 500000000000 : ℝ))
      (E := (cell13051 ⟨18, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41723292976627 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (11051392403 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13051_19 : CellCertificate 13051 (877137927736393 / 10000000000000000 : ℝ) (402349302131153 / 250000000000000000 : ℝ) (162441646801483 / 5000000000000000 : ℝ)
    (cell13051 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · norm_num [cell13051]
  · have h := gap_lower (n := 13051) (a := (41706069029711 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210282447773 / 100000000000000 : ℝ))
      (E := (cell13051 ⟨19, by decide⟩).energy) (xi := (162441646801483 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13051 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13051]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13051])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13051) (a := (41706069029711 / 50000000000000 : ℝ)) (b := (157776310019 / 100000000000000 : ℝ)) (q := (2210282447773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13051])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13051]

theorem cert13052_0 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (84070808718301 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210093235229 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨0, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (84070808718301 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210093235229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_1 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (16807183916931 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105048622999 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨1, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (16807183916931 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105048622999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_2 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (84001055264241 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (69065664251 / 3125000000000 : ℝ))
      (E := (cell13052 ⟨2, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (84001055264241 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (69065664251 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_3 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (10495776965103 / 12500000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210105215793 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨3, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (10495776965103 / 12500000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210105215793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_4 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (2098285022959 / 2500000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105054624603 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨4, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (2098285022959 / 2500000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105054624603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_5 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (20974152705249 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210113248281 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨5, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (20974152705249 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210113248281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_6 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41930922696533 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210117278541 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨6, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41930922696533 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210117278541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_7 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83827104599089 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210121289337 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨7, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83827104599089 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210121289337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_8 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (20948097100943 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (22101252877 / 1000000000000 : ℝ))
      (E := (cell13052 ⟨8, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (20948097100943 / 25000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (22101252877 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_9 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (16751539354401 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210129280413 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨9, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (16751539354401 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210129280413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_10 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83723029668863 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210133274009 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨10, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83723029668863 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210133274009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_11 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (209220967649 / 250000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105068666437 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨11, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (209220967649 / 250000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105068666437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_12 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83653768909653 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210141288739 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨12, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83653768909653 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210141288739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_13 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41809587592319 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210145321699 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨13, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41809587592319 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210145321699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_14 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83584605850349 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105074660513 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨14, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83584605850349 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105074660513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_15 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41775030436379 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442030670029 / 20000000000000 : ℝ))
      (E := (cell13052 ⟨15, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41775030436379 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (442030670029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_16 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41757770109007 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105078677947 / 50000000000000 : ℝ))
      (E := (cell13052 ⟨16, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41757770109007 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (1105078677947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_17 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (41740521926219 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210161343019 / 100000000000000 : ℝ))
      (E := (cell13052 ⟨17, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (41740521926219 / 50000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (2210161343019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_18 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (83446571742529 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (138135335893 / 6250000000000 : ℝ))
      (E := (cell13052 ⟨18, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (83446571742529 / 100000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (138135335893 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13052_19 : CellCertificate 13052 (877111416033299 / 10000000000000000 : ℝ) (804636931258311 / 500000000000000000 : ℝ) (20303614165163 / 625000000000000 : ℝ)
    (cell13052 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · norm_num [cell13052]
  · have h := gap_lower (n := 13052) (a := (16682424770991 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552542348937 / 25000000000000 : ℝ))
      (E := (cell13052 ⟨19, by decide⟩).energy) (xi := (20303614165163 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13052 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13052]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13052])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13052) (a := (16682424770991 / 20000000000000 : ℝ)) (b := (157764081989 / 100000000000000 : ℝ)) (q := (552542348937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13052])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13052]

theorem cert13053_0 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (84070794396173 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2209980146787 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨0, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (84070794396173 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2209980146787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_1 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (16807181053777 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2209984152689 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨1, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (16807181053777 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2209984152689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_2 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (84001040954823 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2209988157903 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨2, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (84001040954823 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2209988157903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_3 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83966201417753 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (552498042701 / 25000000000000 : ℝ))
      (E := (cell13053 ⟨3, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83966201417753 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (552498042701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_4 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (8393138662163 / 10000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2209996199513 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨4, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (8393138662163 / 10000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2209996199513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_5 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41948298265301 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210000193931 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨5, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41948298265301 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210000193931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_6 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83861831109 / 100000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (34531315931 / 1562500000000 : ℝ))
      (E := (cell13053 ⟨6, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83861831109 / 100000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (34531315931 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_7 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83827090321347 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (276251028227 / 12500000000000 : ℝ))
      (E := (cell13053 ⟨7, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83827090321347 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (276251028227 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_8 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83792374132349 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210012219663 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨8, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83792374132349 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210012219663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_9 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (16751536501379 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210016207907 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨9, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (16751536501379 / 20000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210016207907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_10 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (4186150770503 / 5000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210020255159 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨10, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (4186150770503 / 5000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210020255159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_11 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (41844186403549 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210024251571 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨11, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (41844186403549 / 50000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210024251571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_12 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83653754663447 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210028261233 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨12, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83653754663447 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210028261233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_13 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83619160944723 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105016144967 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨13, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83619160944723 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105016144967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_14 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83584591616719 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210036285049 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨14, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83584591616719 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210036285049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_15 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (2610938957669 / 3125000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (69063757869 / 3125000000000 : ℝ))
      (E := (cell13053 ⟨15, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (2610938957669 / 3125000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (69063757869 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_16 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83515525996937 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442008862327 / 20000000000000 : ℝ))
      (E := (cell13053 ⟨16, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83515525996937 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (442008862327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_17 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (8348102963763 / 10000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (69064009209 / 3125000000000 : ℝ))
      (E := (cell13053 ⟨17, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (8348102963763 / 10000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (69064009209 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_18 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83446557533983 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210052321933 / 100000000000000 : ℝ))
      (E := (cell13053 ⟨18, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83446557533983 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (2210052321933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13053_19 : CellCertificate 13053 (175416981644011 / 2000000000000000 : ℝ) (804575267706967 / 500000000000000000 : ℝ) (81208090926543 / 2500000000000000 : ℝ)
    (cell13053 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · norm_num [cell13053]
  · have h := gap_lower (n := 13053) (a := (83412109652667 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105028169707 / 50000000000000 : ℝ))
      (E := (cell13053 ⟨19, by decide⟩).energy) (xi := (81208090926543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13053 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13053]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13053])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13053) (a := (83412109652667 / 100000000000000 : ℝ)) (b := (78875927931 / 50000000000000 : ℝ)) (q := (1105028169707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13053])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13053]

theorem cert13054_0 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (84070780076241 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1104933555933 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨0, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (84070780076241 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1104933555933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_1 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (84035890955311 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552467778231 / 25000000000000 : ℝ))
      (E := (cell13054 ⟨1, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (84035890955311 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552467778231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_2 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (84001026647601 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (110493755667 / 5000000000000 : ℝ))
      (E := (cell13054 ⟨2, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (84001026647601 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (110493755667 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_3 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (20991546779219 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552469780373 / 25000000000000 : ℝ))
      (E := (cell13054 ⟨3, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (20991546779219 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552469780373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_4 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83931372327093 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209883145499 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨4, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83931372327093 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209883145499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_5 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83896582242399 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209887135261 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨5, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83896582242399 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209887135261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_6 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83861816827127 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (138118197269 / 6250000000000 : ℝ))
      (E := (cell13054 ⟨6, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83861816827127 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (138118197269 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_7 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83827076045797 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (88395806319 / 4000000000000 : ℝ))
      (E := (cell13054 ⟨7, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83827076045797 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (88395806319 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_8 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (16758471972623 / 20000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209899205339 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨8, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (16758471972623 / 20000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209899205339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_9 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83757668243973 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209903189139 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨9, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83757668243973 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209903189139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_10 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (20930750288361 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (441981434783 / 20000000000000 : ℝ))
      (E := (cell13054 ⟨10, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (20930750288361 / 25000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (441981434783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_11 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83688358556783 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1104955612027 / 50000000000000 : ℝ))
      (E := (cell13054 ⟨11, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83688358556783 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (1104955612027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_12 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83653740419427 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209915229411 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨12, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83653740419427 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209915229411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_13 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (5226196669187 / 6250000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209919195707 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨13, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (5226196669187 / 6250000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209919195707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_14 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (10448072173159 / 12500000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (55248081119 / 2500000000000 : ℝ))
      (E := (cell13054 ⟨14, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (10448072173159 / 12500000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (55248081119 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_15 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83550032420239 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209927265551 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨15, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83550032420239 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209927265551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_16 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41757755889021 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276241407883 / 12500000000000 : ℝ))
      (E := (cell13054 ⟨16, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41757755889021 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (276241407883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_17 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41740507712501 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209935242047 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨17, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41740507712501 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209935242047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_18 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (83446543327617 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209939265269 / 100000000000000 : ℝ))
      (E := (cell13054 ⟨18, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (83446543327617 / 100000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (2209939265269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13054_19 : CellCertificate 13054 (219264601073941 / 2500000000000000 : ℝ) (1609027227212203 / 1000000000000000000 : ℝ) (162403452396323 / 5000000000000000 : ℝ)
    (cell13054 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · norm_num [cell13054]
  · have h := gap_lower (n := 13054) (a := (41706047726279 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552485819693 / 25000000000000 : ℝ))
      (E := (cell13054 ⟨19, by decide⟩).energy) (xi := (162403452396323 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13054 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13054]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13054])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13054) (a := (41706047726279 / 50000000000000 : ℝ)) (b := (78869815819 / 50000000000000 : ℝ)) (q := (552485819693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13054])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13054]

theorem cert13055_0 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (84070765758507 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (110487703631 / 5000000000000 : ℝ))
      (E := (cell13055 ⟨0, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (84070765758507 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (110487703631 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_1 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (84035876643933 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209758126703 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨1, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (84035876643933 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209758126703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_2 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (84001012342573 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209762122347 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨2, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (84001012342573 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209762122347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_3 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83966172818193 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104883062887 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨3, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83966172818193 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104883062887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_4 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83931358034749 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104885072551 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨4, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83931358034749 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104885072551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_5 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (20974141989097 / 25000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209774130233 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨5, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (20974141989097 / 25000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209774130233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_6 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83861802547443 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (552444536673 / 25000000000000 : ℝ))
      (E := (cell13055 ⟨6, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83861802547443 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (552444536673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_7 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (16765412354487 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104891071913 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨7, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (16765412354487 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104891071913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_8 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (8379234559607 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209786186699 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨8, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (8379234559607 / 10000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209786186699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_9 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83757653983239 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104895083027 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨9, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83757653983239 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104895083027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_10 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (16744597379803 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (69056068891 / 3125000000000 : ℝ))
      (E := (cell13055 ⟨10, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (16744597379803 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (69056068891 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_11 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41844172154327 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104899096111 / 50000000000000 : ℝ))
      (E := (cell13055 ⟨11, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41844172154327 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (1104899096111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_12 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (10456715772199 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (552450548319 / 25000000000000 : ℝ))
      (E := (cell13055 ⟨12, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (10456715772199 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (552450548319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_13 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (16723826494289 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (441961242693 / 20000000000000 : ℝ))
      (E := (cell13055 ⟨13, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (16723826494289 / 20000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (441961242693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_14 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (10448070394501 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (13811313751 / 625000000000 : ℝ))
      (E := (cell13055 ⟨14, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (10448070394501 / 12500000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (13811313751 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_15 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83550018197253 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209814216787 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨15, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83550018197253 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209814216787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_16 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83515497561327 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (441963642037 / 20000000000000 : ℝ))
      (E := (cell13055 ⟨16, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83515497561327 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (441963642037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_17 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (41740500607277 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (110491112167 / 5000000000000 : ℝ))
      (E := (cell13055 ⟨17, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (41740500607277 / 50000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (110491112167 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_18 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83446529123431 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209826262561 / 100000000000000 : ℝ))
      (E := (cell13055 ⟨18, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83446529123431 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (2209826262561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13055_19 : CellCertificate 13055 (877031904259529 / 10000000000000000 : ℝ) (1608903937907083 / 1000000000000000000 : ℝ) (16239072495051 / 500000000000000 : ℝ)
    (cell13055 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · norm_num [cell13055]
  · have h := gap_lower (n := 13055) (a := (83412081254627 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (138114392007 / 6250000000000 : ℝ))
      (E := (cell13055 ⟨19, by decide⟩).energy) (xi := (16239072495051 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13055 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13055]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13055])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13055) (a := (83412081254627 / 100000000000000 : ℝ)) (b := (39431852329 / 25000000000000 : ℝ)) (q := (138114392007 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13055])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13055]

theorem cert13056_0 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (10508843930371 / 12500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209641086897 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨0, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (10508843930371 / 12500000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209641086897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_1 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (336143449339 / 400000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552411269573 / 25000000000000 : ℝ))
      (E := (cell13056 ⟨1, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (336143449339 / 400000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552411269573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_2 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (84000998039739 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104824563517 / 50000000000000 : ℝ))
      (E := (cell13056 ⟨2, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (84000998039739 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (1104824563517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_3 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83966158521703 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441930625147 / 20000000000000 : ℝ))
      (E := (cell13056 ⟨3, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83966158521703 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441930625147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_4 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83931343744597 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209657140387 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨4, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83931343744597 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209657140387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_5 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83896553672569 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209661120887 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨5, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83896553672569 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209661120887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_6 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (1677235765399 / 2000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209665132763 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨6, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (1677235765399 / 2000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209665132763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_7 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83827047501263 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276208647921 / 12500000000000 : ℝ))
      (E := (cell13056 ⟨7, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83827047501263 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (276208647921 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_8 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41896165665607 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209673163743 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨8, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41896165665607 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209673163743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_9 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (20939409931173 / 25000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209677196711 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨9, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (20939409931173 / 25000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209677196711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_10 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83722972646773 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209681172717 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨10, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83722972646773 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209681172717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_11 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (8368833006271 / 10000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (110484260709 / 5000000000000 : ℝ))
      (E := (cell13056 ⟨11, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (8368833006271 / 10000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (110484260709 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_12 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83653711937941 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552422302739 / 25000000000000 : ℝ))
      (E := (cell13056 ⟨12, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83653711937941 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (552422302739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_13 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41809559119041 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (69052913341 / 3125000000000 : ℝ))
      (E := (cell13056 ⟨13, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41809559119041 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (69052913341 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_14 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83584548928927 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209697209421 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨14, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83584548928927 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209697209421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_15 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (326367203033 / 390625000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (220970122191 / 10000000000000 : ℝ))
      (E := (cell13056 ⟨15, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (326367203033 / 390625000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (220970122191 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_16 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41757741673397 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441941042243 / 20000000000000 : ℝ))
      (E := (cell13056 ⟨16, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41757741673397 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (441941042243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_17 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (41740493503143 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (88388369613 / 4000000000000 : ℝ))
      (E := (cell13056 ⟨17, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (41740493503143 / 50000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (88388369613 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_18 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83446514921423 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209713255547 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨18, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83446514921423 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209713255547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13056_19 : CellCertificate 13056 (877005408110451 / 10000000000000000 : ℝ) (1608780667494231 / 1000000000000000000 : ℝ) (81188999757571 / 2500000000000000 : ℝ)
    (cell13056 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · norm_num [cell13056]
  · have h := gap_lower (n := 13056) (a := (83412067058873 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209717261147 / 100000000000000 : ℝ))
      (E := (cell13056 ⟨19, by decide⟩).energy) (xi := (81188999757571 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13056 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13056]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13056])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13056) (a := (83412067058873 / 100000000000000 : ℝ)) (b := (31543037779 / 20000000000000 : ℝ)) (q := (2209717261147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13056])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13056]

theorem cert13057_0 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (672565897037 / 800000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209528096851 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨0, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (672565897037 / 800000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209528096851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_1 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (84035848027761 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209532141297 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨1, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (84035848027761 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209532141297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_2 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (84000983739099 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209536127399 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨2, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (84000983739099 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209536127399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_3 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (16793228845481 / 20000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104770060689 / 50000000000000 : ℝ))
      (E := (cell13057 ⟨3, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (16793228845481 / 20000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104770060689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_4 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83931329456637 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (276193016419 / 12500000000000 : ℝ))
      (E := (cell13057 ⟨4, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83931329456637 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (276193016419 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_5 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (4194826969547 / 5000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (34524190081 / 1562500000000 : ℝ))
      (E := (cell13057 ⟨5, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (4194826969547 / 5000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (34524190081 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_6 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83861773994647 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209552172501 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨6, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83861773994647 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209552172501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_7 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (2095675830807 / 2500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (441911232117 / 20000000000000 : ℝ))
      (E := (cell13057 ⟨7, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (2095675830807 / 2500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (441911232117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_8 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (16758463413709 / 20000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (276195024313 / 12500000000000 : ℝ))
      (E := (cell13057 ⟨8, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (16758463413709 / 20000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (276195024313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_9 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (20939406367083 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209564223053 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨9, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (20939406367083 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209564223053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_10 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (20930739599179 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (17262251521 / 781250000000 : ℝ))
      (E := (cell13057 ⟨10, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (20930739599179 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (17262251521 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_11 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83688315818951 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104786115913 / 50000000000000 : ℝ))
      (E := (cell13057 ⟨11, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83688315818951 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104786115913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_12 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (41826848850237 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209576224323 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨12, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (41826848850237 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209576224323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_13 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (41809552003451 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209580236047 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨13, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (41809552003451 / 50000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209580236047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_14 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (20896133676007 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552396053593 / 25000000000000 : ℝ))
      (E := (cell13057 ⟨14, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (20896133676007 / 25000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552396053593 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_15 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (3341999590313 / 4000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104794140459 / 50000000000000 : ℝ))
      (E := (cell13057 ⟨15, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (3341999590313 / 4000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (1104794140459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_16 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (2087886728361 / 2500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552398066539 / 25000000000000 : ℝ))
      (E := (cell13057 ⟨16, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (2087886728361 / 2500000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552398066539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_17 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83480972800197 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (441919258249 / 20000000000000 : ℝ))
      (E := (cell13057 ⟨17, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83480972800197 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (441919258249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_18 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83446500721593 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209600302493 / 100000000000000 : ℝ))
      (E := (cell13057 ⟨18, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83446500721593 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (2209600302493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13057_19 : CellCertificate 13057 (175395783169527 / 2000000000000000 : ℝ) (321731483193861 / 200000000000000000 : ℝ) (324730552179429 / 10000000000000000 : ℝ)
    (cell13057 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · norm_num [cell13057]
  · have h := gap_lower (n := 13057) (a := (83412052865297 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552401076041 / 25000000000000 : ℝ))
      (E := (cell13057 ⟨19, by decide⟩).energy) (xi := (324730552179429 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13057 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13057]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13057])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13057) (a := (83412052865297 / 100000000000000 : ℝ)) (b := (19712871297 / 12500000000000 : ℝ)) (q := (552401076041 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13057])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13057]

theorem cert13058_0 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (84070722818477 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209415160329 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨0, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (84070722818477 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209415160329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_1 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (42017916861483 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104709599991 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨1, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (42017916861483 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104709599991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_2 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (21000242360163 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104711590669 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨2, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (21000242360163 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104711590669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_3 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (839661299353 / 1000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209427170617 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨3, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (839661299353 / 1000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209427170617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_4 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (20982828792717 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104715587969 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨4, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (20982828792717 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104715587969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_5 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83896525111501 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104717602583 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨5, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83896525111501 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104717602583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_6 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83861759721533 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552359801981 / 25000000000000 : ℝ))
      (E := (cell13058 ⟨6, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83861759721533 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552359801981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_7 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (16765403793097 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104721624753 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨7, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (16765403793097 / 20000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104721624753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_8 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (81828420711 / 97656250000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209447220951 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨8, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (81828420711 / 97656250000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209447220951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_9 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83757611214159 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209451245083 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨9, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83757611214159 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209451245083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_10 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (20930736037211 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104727635213 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨10, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (20930736037211 / 25000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104727635213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_11 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (2615259424293 / 3125000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209459245161 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨11, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (2615259424293 / 3125000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209459245161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_12 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83653683465191 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104731645753 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨12, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83653683465191 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104731645753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_13 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (5226193111119 / 6250000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (138091706189 / 6250000000000 : ℝ))
      (E := (cell13058 ⟨13, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (5226193111119 / 6250000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (138091706189 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_14 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (8358452048131 / 10000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552367818297 / 25000000000000 : ℝ))
      (E := (cell13058 ⟨14, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (8358452048131 / 10000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (552367818297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_15 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83549975541381 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (88379011097 / 4000000000000 : ℝ))
      (E := (cell13058 ⟨15, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83549975541381 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (88379011097 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_16 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41757727462133 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209479316791 / 100000000000000 : ℝ))
      (E := (cell13058 ⟨16, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41757727462133 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (2209479316791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_17 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83480958596287 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (110474166893 / 5000000000000 : ℝ))
      (E := (cell13058 ⟨17, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83480958596287 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (110474166893 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_18 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (83446486523941 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104743672567 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨18, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (83446486523941 / 100000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104743672567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13058_19 : CellCertificate 13058 (438476213735091 / 5000000000000000 : ℝ) (402133545831991 / 250000000000000000 : ℝ) (64941021869489 / 2000000000000000 : ℝ)
    (cell13058 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · norm_num [cell13058]
  · have h := gap_lower (n := 13058) (a := (41706019336949 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104745671439 / 50000000000000 : ℝ))
      (E := (cell13058 ⟨19, by decide⟩).energy) (xi := (64941021869489 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13058 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13058]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13058])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13058) (a := (41706019336949 / 50000000000000 : ℝ)) (b := (157690753757 / 100000000000000 : ℝ)) (q := (1104745671439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13058])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13058]

theorem cert13059_0 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (21017677127381 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209302219487 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨0, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (21017677127381 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209302219487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_1 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (16807163884073 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (552326563587 / 25000000000000 : ℝ))
      (E := (cell13059 ⟨1, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (16807163884073 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (552326563587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_2 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (84000955144397 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104655115479 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨2, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (84000955144397 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104655115479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_3 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41983057822693 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104657136727 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨3, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41983057822693 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104657136727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_4 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83931300887289 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (552329568537 / 25000000000000 : ℝ))
      (E := (cell13059 ⟨4, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83931300887289 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (552329568537 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_5 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (20974127708563 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104661149397 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨5, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (20974127708563 / 25000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104661149397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_6 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (5241359090663 / 6250000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209326297017 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨6, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (5241359090663 / 6250000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209326297017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_7 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41913502350439 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209330276103 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨7, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41913502350439 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209330276103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_8 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83792288549769 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209334301117 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨8, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83792288549769 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209334301117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_9 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83757596962171 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (441867664171 / 20000000000000 : ℝ))
      (E := (cell13059 ⟨9, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83757596962171 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (441867664171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_10 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41861464951579 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (552335585463 / 25000000000000 : ℝ))
      (E := (cell13059 ⟨10, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41861464951579 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (552335585463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_11 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (16737657467597 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (69042072259 / 3125000000000 : ℝ))
      (E := (cell13059 ⟨11, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (16737657467597 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (69042072259 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_12 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (8365366923209 / 10000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (110467517719 / 5000000000000 : ℝ))
      (E := (cell13059 ⟨12, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (8365366923209 / 10000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (110467517719 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_13 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (5226192221943 / 6250000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209354357691 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨13, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (5226192221943 / 6250000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209354357691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_14 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83584506260773 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209358385869 / 100000000000000 : ℝ))
      (E := (cell13059 ⟨14, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83584506260773 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (2209358385869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_15 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41774980663559 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (69042574563 / 3125000000000 : ℝ))
      (E := (cell13059 ⟨15, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41774980663559 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (69042574563 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_16 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (83515440716271 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (27617079539 / 1250000000000 : ℝ))
      (E := (cell13059 ⟨16, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (83515440716271 / 100000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (27617079539 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_17 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (41740472197277 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (220937038017 / 10000000000000 : ℝ))
      (E := (cell13059 ⟨17, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (41740472197277 / 50000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (220937038017 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_18 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (16689294465693 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (138085898967 / 6250000000000 : ℝ))
      (E := (cell13059 ⟨18, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (16689294465693 / 20000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (138085898967 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13059_19 : CellCertificate 13059 (438462971488599 / 5000000000000000 : ℝ) (402102742391467 / 250000000000000000 : ℝ) (81169917633331 / 2500000000000000 : ℝ)
    (cell13059 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · norm_num [cell13059]
  · have h := gap_lower (n := 13059) (a := (3336480979387 / 4000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104689217789 / 50000000000000 : ℝ))
      (E := (cell13059 ⟨19, by decide⟩).energy) (xi := (81169917633331 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13059 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13059]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13059])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13059) (a := (3336480979387 / 4000000000000 : ℝ)) (b := (157678539039 / 100000000000000 : ℝ)) (q := (1104689217789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13059])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13059]

theorem cert13060_0 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (21017673550691 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209189332171 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨0, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (21017673550691 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209189332171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_1 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (84035805119957 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276149170283 / 12500000000000 : ℝ))
      (E := (cell13060 ⟨1, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (84035805119957 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276149170283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_2 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (16800188170067 / 20000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276149666769 / 12500000000000 : ℝ))
      (E := (cell13060 ⟨2, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (16800188170067 / 20000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276149666769 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_3 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (2623940667427 / 3125000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104600685987 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨3, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (2623940667427 / 3125000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104600685987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_4 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83931286605901 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209205368041 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨4, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83931286605901 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209205368041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_5 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (10487062069899 / 12500000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209209388107 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨5, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (10487062069899 / 12500000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209209388107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_6 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83861731181871 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209213381797 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨6, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83861731181871 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209213381797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_7 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41913495219229 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104608707203 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨7, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41913495219229 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104608707203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_8 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83792274293661 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209221376971 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨8, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83792274293661 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209221376971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_9 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (5234848919523 / 6250000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104612696159 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨9, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (5234848919523 / 6250000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104612696159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_10 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (10465364457457 / 12500000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276153676121 / 12500000000000 : ℝ))
      (E := (cell13060 ⟨10, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (10465364457457 / 12500000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (276153676121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_11 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41844136550389 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209233433207 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨11, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41844136550389 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209233433207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_12 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (20913413750293 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441847482589 / 20000000000000 : ℝ))
      (E := (cell13060 ⟨12, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (20913413750293 / 25000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441847482589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_13 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83619061326453 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (11046207351 / 500000000000 : ℝ))
      (E := (cell13060 ⟨13, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83619061326453 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (11046207351 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_14 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83584492042417 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (220924543607 / 10000000000000 : ℝ))
      (E := (cell13060 ⟨14, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83584492042417 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (220924543607 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_15 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41774973557517 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104624745151 / 50000000000000 : ℝ))
      (E := (cell13060 ⟨15, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41774973557517 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (1104624745151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_16 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (41757713255227 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441850692673 / 20000000000000 : ℝ))
      (E := (cell13060 ⟨16, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (41757713255227 / 50000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (441850692673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_17 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83480930194999 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209257476419 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨17, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83480930194999 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209257476419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_18 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83446458135167 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (552315368943 / 25000000000000 : ℝ))
      (E := (cell13060 ⟨18, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83446458135167 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (552315368943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13060_19 : CellCertificate 13060 (175379892473557 / 2000000000000000 : ℝ) (1608287774678681 / 1000000000000000000 : ℝ) (162327117868029 / 5000000000000000 : ℝ)
    (cell13060 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · norm_num [cell13060]
  · have h := gap_lower (n := 13060) (a := (83412010297627 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209265523977 / 100000000000000 : ℝ))
      (E := (cell13060 ⟨19, by decide⟩).energy) (xi := (162327117868029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13060 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13060]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13060])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13060) (a := (83412010297627 / 100000000000000 : ℝ)) (b := (157666326221 / 100000000000000 : ℝ)) (q := (2209265523977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13060])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13060]

theorem cert13061_0 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (42035339949099 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104538220269 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨0, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (42035339949099 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104538220269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_1 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (84035790821741 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276135058233 / 12500000000000 : ℝ))
      (E := (cell13061 ⟨1, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (84035790821741 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276135058233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_2 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (328128619369 / 390625000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209084490923 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨2, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (328128619369 / 390625000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209084490923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_3 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (20991521768033 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (110454423309 / 5000000000000 : ℝ))
      (E := (cell13061 ⟨3, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (20991521768033 / 25000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (110454423309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_4 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41965636163351 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (110454622881 / 5000000000000 : ℝ))
      (E := (cell13061 ⟨4, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41965636163351 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (110454622881 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_5 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (1048706028579 / 1250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552274118277 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨5, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (1048706028579 / 1250000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552274118277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_6 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (83861716915321 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209100520251 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨6, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (83861716915321 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209100520251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_7 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (3353079047129 / 4000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552276122597 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨7, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (3353079047129 / 4000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552276122597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_8 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41896130019869 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209108506547 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨8, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41896130019869 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209108506547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_9 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (83757568464751 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (88364500701 / 4000000000000 : ℝ))
      (E := (cell13061 ⟨9, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (83757568464751 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (88364500701 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_10 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (83722901418337 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (441823305971 / 20000000000000 : ℝ))
      (E := (cell13061 ⟨10, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (83722901418337 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (441823305971 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_11 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (83688258865753 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209120549819 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨11, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (83688258865753 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209120549819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_12 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (16730728154487 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (220912452533 / 10000000000000 : ℝ))
      (E := (cell13061 ⟨12, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (16730728154487 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (220912452533 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_13 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (83619047103999 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552282144601 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨13, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (83619047103999 / 100000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552282144601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_14 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (261201493207 / 312500000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276141574789 / 12500000000000 : ℝ))
      (E := (cell13061 ⟨14, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (261201493207 / 312500000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (276141574789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_15 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (8354993290513 / 10000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209136590283 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨15, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (8354993290513 / 10000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209136590283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_16 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (652464158647 / 781250000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552285154381 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨16, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (652464158647 / 781250000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552285154381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_17 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (41740457998811 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209144626607 / 100000000000000 : ℝ))
      (E := (cell13061 ⟨17, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (41740457998811 / 50000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (2209144626607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_18 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (16689288788809 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552287155509 / 25000000000000 : ℝ))
      (E := (cell13061 ⟨18, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (16689288788809 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (552287155509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13061_19 : CellCertificate 13061 (109609123205131 / 1250000000000000 : ℝ) (100510287416379 / 62500000000000000 : ℝ) (324628804954639 / 10000000000000000 : ℝ)
    (cell13061 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · norm_num [cell13061]
  · have h := gap_lower (n := 13061) (a := (16682399222551 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104576304037 / 50000000000000 : ℝ))
      (E := (cell13061 ⟨19, by decide⟩).energy) (xi := (324628804954639 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13061 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13061]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13061])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13061) (a := (16682399222551 / 20000000000000 : ℝ)) (b := (78827057651 / 50000000000000 : ℝ)) (q := (1104576304037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13061])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13061]

theorem cert13062_0 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (3362826623833 / 4000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104481801217 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨0, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (3362826623833 / 4000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104481801217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_1 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (42017888262859 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2208967565147 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨1, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (42017888262859 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2208967565147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_2 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (5250057016799 / 6250000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (138060724093 / 6250000000000 : ℝ))
      (E := (cell13062 ⟨2, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (5250057016799 / 6250000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (138060724093 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_3 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (8396607278879 / 10000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2208975613987 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨3, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (8396607278879 / 10000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2208975613987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_4 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (20982814512423 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104489800413 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨4, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (20982814512423 / 25000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104489800413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_5 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83896468015637 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104491805879 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨5, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83896468015637 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104491805879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_6 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83861702650959 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2208987654393 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨6, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83861702650959 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2208987654393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_7 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41913480960089 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2208991620069 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨7, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41913480960089 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2208991620069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_8 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (20948061447 / 25000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (441799126363 / 20000000000000 : ℝ))
      (E := (cell13062 ⟨8, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (20948061447 / 25000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (441799126363 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_9 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83757554219317 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (88359985537 / 4000000000000 : ℝ))
      (E := (cell13062 ⟨9, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83757554219317 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (88359985537 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_10 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41861443589601 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104501823217 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨10, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41861443589601 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104501823217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_11 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83688244632911 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552251915531 / 25000000000000 : ℝ))
      (E := (cell13062 ⟨11, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83688244632911 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552251915531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_12 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (2091340663647 / 2500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104505845767 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨12, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (2091340663647 / 2500000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104505845767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_13 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41809516441863 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104507841151 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨13, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41809516441863 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104507841151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_14 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83584463612243 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209019698077 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨14, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83584463612243 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209019698077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_15 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83549918697403 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209023744157 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨15, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83549918697403 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209023744157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_16 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (16703079621071 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104513854581 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨16, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (16703079621071 / 20000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104513854581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_17 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83480901802421 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552257928563 / 25000000000000 : ℝ))
      (E := (cell13062 ⟨17, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83480901802421 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (552257928563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_18 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (41723214877549 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209035764001 / 100000000000000 : ℝ))
      (E := (cell13062 ⟨18, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (41723214877549 / 50000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (2209035764001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13062_19 : CellCertificate 13062 (876846512796091 / 10000000000000000 : ℝ) (804020720755841 / 500000000000000000 : ℝ) (162301689094029 / 5000000000000000 : ℝ)
    (cell13062 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · norm_num [cell13062]
  · have h := gap_lower (n := 13062) (a := (83411981930057 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104519873081 / 50000000000000 : ℝ))
      (E := (cell13062 ⟨19, by decide⟩).energy) (xi := (162301689094029 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13062 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13062]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13062])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13062) (a := (83411981930057 / 100000000000000 : ℝ)) (b := (78820953141 / 50000000000000 : ℝ)) (q := (1104519873081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13062])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13062]

theorem cert13063_0 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (16814130259129 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208850760013 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨0, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (16814130259129 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208850760013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_1 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (42017881115943 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552213693963 / 25000000000000 : ℝ))
      (E := (cell13063 ⟨1, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (42017881115943 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552213693963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_2 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (16800179596259 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208858733629 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨2, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (16800179596259 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208858733629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_3 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83966058507637 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208862757481 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨3, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83966058507637 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208862757481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_4 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83931243774871 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208866797657 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨4, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83931243774871 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208866797657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_5 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41948226873571 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104435402029 / 50000000000000 : ℝ))
      (E := (cell13063 ⟨5, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41948226873571 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (1104435402029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_6 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83861688388783 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (88354991369 / 4000000000000 : ℝ))
      (E := (cell13063 ⟨6, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83861688388783 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (88354991369 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_7 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20956736916079 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (44177576069 / 2000000000000 : ℝ))
      (E := (cell13063 ⟨7, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20956736916079 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (44177576069 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_8 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (5237014471153 / 6250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552220702701 / 25000000000000 : ℝ))
      (E := (cell13063 ⟨8, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (5237014471153 / 6250000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (552220702701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_9 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20939384994017 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208886813071 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨9, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20939384994017 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208886813071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_10 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (334891491769 / 400000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (138055676049 / 6250000000000 : ℝ))
      (E := (cell13063 ⟨10, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (334891491769 / 400000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (138055676049 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_11 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83688230402251 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (88355793129 / 4000000000000 : ℝ))
      (E := (cell13063 ⟨11, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83688230402251 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (88355793129 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_12 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41826806160753 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (276112356679 / 12500000000000 : ℝ))
      (E := (cell13063 ⟨12, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41826806160753 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (276112356679 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_13 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83619018665633 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441780568009 / 20000000000000 : ℝ))
      (E := (cell13063 ⟨13, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83619018665633 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441780568009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_14 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (3343377976017 / 4000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (220890685171 / 10000000000000 : ℝ))
      (E := (cell13063 ⟨14, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (3343377976017 / 4000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (220890685171 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_15 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (16709980898371 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (69028465429 / 3125000000000 : ℝ))
      (E := (cell13063 ⟨15, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (16709980898371 / 20000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (69028465429 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_16 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83515383906071 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208914912937 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨16, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83515383906071 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208914912937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_17 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (20870221902349 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208918914081 / 100000000000000 : ℝ))
      (E := (cell13063 ⟨17, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (20870221902349 / 25000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (2208918914081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_18 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (41723207784163 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441784580333 / 20000000000000 : ℝ))
      (E := (cell13063 ⟨18, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (41723207784163 / 50000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (441784580333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13063_19 : CellCertificate 13063 (876820043832019 / 10000000000000000 : ℝ) (803959151611601 / 500000000000000000 : ℝ) (32457795543531 / 1000000000000000 : ℝ)
    (cell13063 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · norm_num [cell13063]
  · have h := gap_lower (n := 13063) (a := (83411967749533 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (3451448341 / 156250000000 : ℝ))
      (E := (cell13063 ⟨19, by decide⟩).energy) (xi := (32457795543531 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13063 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13063]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13063])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13063) (a := (83411967749533 / 100000000000000 : ℝ)) (b := (157629699161 / 100000000000000 : ℝ)) (q := (3451448341 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13063])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13063]

theorem cert13064_0 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (84070636997657 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104368956639 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨0, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (84070636997657 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104368956639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_1 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16807149588049 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208741924377 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨1, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16807149588049 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208741924377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_2 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16800176739199 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (276093241919 / 12500000000000 : ℝ))
      (E := (cell13064 ⟨2, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16800176739199 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (276093241919 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_3 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41983022114337 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (110437497729 / 5000000000000 : ℝ))
      (E := (cell13064 ⟨3, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41983022114337 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (110437497729 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_4 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41965614751119 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (27609424153 / 1250000000000 : ℝ))
      (E := (cell13064 ⟨4, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41965614751119 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (27609424153 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_5 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83896439480833 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208757992051 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨5, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83896439480833 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208757992051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_6 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41930837064397 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208761967733 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨6, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41930837064397 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208761967733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_7 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (1047836667633 / 1250000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104382991261 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨7, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (1047836667633 / 1250000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104382991261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_8 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83792217291079 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (138048124093 / 6250000000000 : ℝ))
      (E := (cell13064 ⟨8, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83792217291079 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (138048124093 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_9 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83757525735001 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208773983413 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨9, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83757525735001 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208773983413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_10 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (2093071467687 / 2500000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (220877798283 / 10000000000000 : ℝ))
      (E := (cell13064 ⟨10, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (2093071467687 / 2500000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (220877798283 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_11 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (20922054043443 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208781990023 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨11, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (20922054043443 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208781990023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_12 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83653598099313 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (552196502757 / 25000000000000 : ℝ))
      (E := (cell13064 ⟨12, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83653598099313 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (552196502757 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_13 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83619004449719 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441758010327 / 20000000000000 : ℝ))
      (E := (cell13064 ⟨13, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83619004449719 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441758010327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_14 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41792217595393 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441758811843 / 20000000000000 : ℝ))
      (E := (cell13064 ⟨14, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41792217595393 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (441758811843 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_15 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (16709978057697 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208798038999 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨15, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (16709978057697 / 20000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208798038999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_16 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (20878842427241 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208802054193 / 100000000000000 : ℝ))
      (E := (cell13064 ⟨16, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (20878842427241 / 25000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (2208802054193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_17 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (41740436709273 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (220880605137 / 10000000000000 : ℝ))
      (E := (cell13064 ⟨17, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (41740436709273 / 50000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (220880605137 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_18 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83446401383729 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104405046649 / 50000000000000 : ℝ))
      (E := (cell13064 ⟨18, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83446401383729 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (1104405046649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13064_19 : CellCertificate 13064 (27399799335873 / 312500000000000 : ℝ) (160779518379229 / 100000000000000000 : ℝ) (81138134173847 / 2500000000000000 : ℝ)
    (cell13064 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · norm_num [cell13064]
  · have h := gap_lower (n := 13064) (a := (83411953571183 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (552203516933 / 25000000000000 : ℝ))
      (E := (cell13064 ⟨19, by decide⟩).energy) (xi := (81138134173847 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13064 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13064]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13064])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13064) (a := (83411953571183 / 100000000000000 : ℝ)) (b := (157617493937 / 100000000000000 : ℝ)) (q := (552203516933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13064])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13064]

theorem cert13065_0 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (4203531135093 / 5000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (88345004803 / 4000000000000 : ℝ))
      (E := (cell13065 ⟨0, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (4203531135093 / 5000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (88345004803 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_1 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (16807146730159 / 20000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276078640807 / 12500000000000 : ℝ))
      (E := (cell13065 ⟨1, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (16807146730159 / 20000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276078640807 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_2 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (42000434706443 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104316566381 / 50000000000000 : ℝ))
      (E := (cell13065 ⟨2, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (42000434706443 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104316566381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_3 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (839660299519 / 1000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104318573683 / 50000000000000 : ℝ))
      (E := (cell13065 ⟨3, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (839660299519 / 1000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104318573683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_4 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83931215231793 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208641178389 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨4, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83931215231793 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208641178389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_5 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (10487053152089 / 12500000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (552161293933 / 25000000000000 : ℝ))
      (E := (cell13065 ⟨5, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (10487053152089 / 12500000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (552161293933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_6 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (8386165987099 / 10000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208649146933 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨6, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (8386165987099 / 10000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208649146933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_7 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83826919159149 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208653157287 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨7, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83826919159149 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208653157287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_8 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (16758440609179 / 20000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208657213897 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨8, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (16758440609179 / 20000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208657213897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_9 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41878755748059 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (138041325469 / 6250000000000 : ℝ))
      (E := (cell13065 ⟨9, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41878755748059 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (138041325469 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_10 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (20930711118723 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (44173304053 / 2000000000000 : ℝ))
      (E := (cell13065 ⟨10, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (20930711118723 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (44173304053 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_11 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (41844100973737 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104334602809 / 50000000000000 : ℝ))
      (E := (cell13065 ⟨11, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (41844100973737 / 50000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104334602809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_12 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83653583879299 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104336611223 / 50000000000000 : ℝ))
      (E := (cell13065 ⟨12, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83653583879299 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104336611223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_13 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (5226186889749 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208677258923 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨13, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (5226186889749 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208677258923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_14 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (20896105245831 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208681262419 / 100000000000000 : ℝ))
      (E := (cell13065 ⟨14, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (20896105245831 / 25000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (2208681262419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_15 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83549876087291 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104342619083 / 50000000000000 : ℝ))
      (E := (cell13065 ⟨15, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83549876087291 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (1104342619083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_16 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (5219709719627 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (220868924937 / 10000000000000 : ℝ))
      (E := (cell13065 ⟨16, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (5219709719627 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (220868924937 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_17 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (5217553701867 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441738660169 / 20000000000000 : ℝ))
      (E := (cell13065 ⟨17, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (5217553701867 / 6250000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441738660169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_18 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83446387201307 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276087160079 / 12500000000000 : ℝ))
      (E := (cell13065 ⟨18, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83446387201307 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (276087160079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13065_19 : CellCertificate 13065 (876767117542949 / 10000000000000000 : ℝ) (321534416642923 / 200000000000000000 : ℝ) (64905424393457 / 2000000000000000 : ℝ)
    (cell13065 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · norm_num [cell13065]
  · have h := gap_lower (n := 13065) (a := (83411939395007 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441740261901 / 20000000000000 : ℝ))
      (E := (cell13065 ⟨19, by decide⟩).energy) (xi := (64905424393457 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13065 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13065]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13065])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13065) (a := (83411939395007 / 100000000000000 : ℝ)) (b := (157605290611 / 100000000000000 : ℝ)) (q := (441740261901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13065])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13065]

theorem cert13066_0 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (42035304204127 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208512322559 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨0, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (42035304204127 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208512322559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_1 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (42017859681767 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104258191047 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨1, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (42017859681767 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104258191047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_2 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (16800171026393 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208520383753 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨2, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (16800171026393 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208520383753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_3 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83966015677313 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104262196879 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨3, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83966015677313 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104262196879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_4 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (16786240192707 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (220852836229 / 10000000000000 : ℝ))
      (E := (cell13066 ⟨4, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (16786240192707 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (220852836229 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_5 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (10487051369347 / 12500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552133103267 / 25000000000000 : ℝ))
      (E := (cell13066 ⟨5, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (10487051369347 / 12500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552133103267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_6 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20965411403843 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (220853637981 / 10000000000000 : ℝ))
      (E := (cell13066 ⟨6, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20965411403843 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (220853637981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_7 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (41913452454921 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104270192877 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨7, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (41913452454921 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104270192877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_8 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83792188802893 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104272219 / 50000000000 : ℝ))
      (E := (cell13066 ⟨8, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83792188802893 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104272219 / 50000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_9 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (10469687157427 / 12500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208548427291 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨9, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (10469687157427 / 12500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208548427291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_10 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (16744566048897 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104276209083 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨10, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (16744566048897 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104276209083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_11 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20922046930839 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208556416911 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨11, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20922046930839 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208556416911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_12 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (16730713932293 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104280214781 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨12, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (16730713932293 / 20000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104280214781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_13 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20904744006107 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552141115477 / 25000000000000 : ℝ))
      (E := (cell13066 ⟨13, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20904744006107 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552141115477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_14 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (2089610169451 / 2500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104284230661 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨14, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (2089610169451 / 2500000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104284230661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_15 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (41774930944137 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552143122807 / 25000000000000 : ℝ))
      (E := (cell13066 ⟨15, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (41774930944137 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (552143122807 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_16 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83515341321277 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104288249233 / 50000000000000 : ℝ))
      (E := (cell13066 ⟨16, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83515341321277 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (1104288249233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_17 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (20870211260843 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208580487779 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨17, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (20870211260843 / 25000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208580487779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_18 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (83446373021057 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208584521937 / 100000000000000 : ℝ))
      (E := (cell13066 ⟨18, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (83446373021057 / 100000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (2208584521937 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13066_19 : CellCertificate 13066 (438370330108081 / 5000000000000000 : ℝ) (803774500742923 / 500000000000000000 : ℝ) (81125427812499 / 2500000000000000 : ℝ)
    (cell13066 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · norm_num [cell13066]
  · have h := gap_lower (n := 13066) (a := (41705962610501 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (276073568373 / 12500000000000 : ℝ))
      (E := (cell13066 ⟨19, by decide⟩).energy) (xi := (81125427812499 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13066 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13066]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13066])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13066) (a := (41705962610501 / 50000000000000 : ℝ)) (b := (157593089183 / 100000000000000 : ℝ)) (q := (276073568373 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13066])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13066]

theorem cert13067_0 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (84070594116839 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208399578577 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨0, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (84070594116839 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208399578577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_1 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (1313057891851 / 1562500000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (44168071511 / 2000000000000 : ℝ))
      (E := (cell13067 ⟨1, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (1313057891851 / 1562500000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (44168071511 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_2 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (84000840853233 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441681526087 / 20000000000000 : ℝ))
      (E := (cell13067 ⟨2, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (84000840853233 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441681526087 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_3 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41983000702457 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104205817921 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨3, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41983000702457 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104205817921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_4 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83931186697463 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (138025974989 / 6250000000000 : ℝ))
      (E := (cell13067 ⟨4, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83931186697463 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (138025974989 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_5 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41948198347513 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208419646097 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨5, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41948198347513 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208419646097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_6 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41930815680969 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208423666369 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨6, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41930815680969 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208423666369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_7 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41913445331359 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104213833963 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨7, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41913445331359 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104213833963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_8 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (3351686982483 / 4000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208431657799 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨8, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (3351686982483 / 4000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208431657799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_9 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83757483024897 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208435700829 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨9, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83757483024897 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208435700829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_10 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83722816016259 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (110421984373 / 5000000000000 : ℝ))
      (E := (cell13067 ⟨10, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83722816016259 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (110421984373 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_11 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41844086750709 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441688736401 / 20000000000000 : ℝ))
      (E := (cell13067 ⟨11, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41844086750709 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441688736401 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_12 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83653555445809 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276055961313 / 12500000000000 : ℝ))
      (E := (cell13067 ⟨12, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83653555445809 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (276055961313 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_13 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83618961815049 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441690343749 / 20000000000000 : ℝ))
      (E := (cell13067 ⟨13, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83618961815049 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (441690343749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_14 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83584392574933 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (22084557141 / 1000000000000 : ℝ))
      (E := (cell13067 ⟨14, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83584392574933 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (22084557141 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_15 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83549847691433 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104229869997 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨15, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83549847691433 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104229869997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_16 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (10439415891337 / 12500000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104231871633 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨16, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (10439415891337 / 12500000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104231871633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_17 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (41740415429523 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (110423386433 / 5000000000000 : ℝ))
      (E := (cell13067 ⟨17, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (41740415429523 / 50000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (110423386433 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_18 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83446358842981 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104235879473 / 50000000000000 : ℝ))
      (E := (cell13067 ⟨18, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83446358842981 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (1104235879473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13067_19 : CellCertificate 13067 (876714206766681 / 10000000000000000 : ℝ) (200928242325207 / 125000000000000000 : ℝ) (162238152271257 / 5000000000000000 : ℝ)
    (cell13067 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · norm_num [cell13067]
  · have h := gap_lower (n := 13067) (a := (83411911049171 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208475780167 / 100000000000000 : ℝ))
      (E := (cell13067 ⟨19, by decide⟩).energy) (xi := (162238152271257 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13067 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13067]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13067])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13067) (a := (83411911049171 / 100000000000000 : ℝ)) (b := (157580889651 / 100000000000000 : ℝ)) (q := (2208475780167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13067])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13067]

theorem cert13068_0 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (42035289913807 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208286888131 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨0, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (42035289913807 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208286888131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_1 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (42017845397791 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208290880437 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨1, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (42017845397791 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208290880437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_2 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (84000826576689 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (276036859101 / 12500000000000 : ℝ))
      (E := (cell13068 ⟨2, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (84000826576689 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (276036859101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_3 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41982993567351 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208298873619 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨3, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41982993567351 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208298873619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_4 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41965586216789 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208302890989 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨4, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41965586216789 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208302890989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_5 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41948191218731 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208306932783 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨5, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41948191218731 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208306932783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_6 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (2620675534709 / 3125000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208310890637 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨6, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (2620675534709 / 3125000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208310890637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_7 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41913438208889 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104157472897 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨7, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41913438208889 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104157472897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_8 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41896080161719 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208318931329 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨8, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41896080161719 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208318931329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_9 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83757468792559 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104161485033 / 50000000000000 : ℝ))
      (E := (cell13068 ⟨9, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83757468792559 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (1104161485033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_10 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41861400895107 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208326952451 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨10, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41861400895107 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208326952451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_11 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83688159281659 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (5520827357 / 250000000000 : ℝ))
      (E := (cell13068 ⟨11, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83688159281659 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (5520827357 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_12 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (20913385308083 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208334947147 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨12, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (20913385308083 / 25000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208334947147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_13 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (10452368450981 / 12500000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208338971283 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨13, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (10452368450981 / 12500000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208338971283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_14 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41792189187001 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (110417148129 / 5000000000000 : ℝ))
      (E := (cell13068 ⟨14, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41792189187001 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (110417148129 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_15 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (83549833496767 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208346984463 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨15, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (83549833496767 / 100000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208346984463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_16 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (8351531294229 / 10000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (220835098377 / 10000000000000 : ℝ))
      (E := (cell13068 ⟨16, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (8351531294229 / 10000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (220835098377 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_17 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41740408338447 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (220835502349 / 10000000000000 : ℝ))
      (E := (cell13068 ⟨17, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41740408338447 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (220835502349 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_18 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (41723172333539 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208359049927 / 100000000000000 : ℝ))
      (E := (cell13068 ⟨18, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (41723172333539 / 50000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (2208359049927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13068_19 : CellCertificate 13068 (876687757193613 / 10000000000000000 : ℝ) (401825723639429 / 250000000000000000 : ℝ) (81112725460959 / 2500000000000000 : ℝ)
    (cell13068 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · norm_num [cell13068]
  · have h := gap_lower (n := 13068) (a := (8341189687951 / 10000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (552090766837 / 25000000000000 : ℝ))
      (E := (cell13068 ⟨19, by decide⟩).energy) (xi := (81112725460959 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13068 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13068]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13068])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13068) (a := (8341189687951 / 10000000000000 : ℝ)) (b := (31513738403 / 20000000000000 : ℝ)) (q := (552090766837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13068])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13068]

theorem cert13069_0 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (42035282770289 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (220817413553 / 10000000000000 : ℝ))
      (E := (cell13069 ⟨0, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (42035282770289 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (220817413553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_1 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (84035676514889 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441635636203 / 20000000000000 : ℝ))
      (E := (cell13069 ⟨1, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (84035676514889 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441635636203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_2 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (84000812302333 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441636433753 / 20000000000000 : ℝ))
      (E := (cell13069 ⟨2, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (84000812302333 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441636433753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_3 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83965972866677 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552046541251 / 25000000000000 : ℝ))
      (E := (cell13069 ⟨3, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83965972866677 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552046541251 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_4 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41965579085939 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208190177849 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨4, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41965579085939 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208190177849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_5 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41948184091041 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552048553791 / 25000000000000 : ℝ))
      (E := (cell13069 ⟨5, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41948184091041 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552048553791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_6 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41930801430811 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552049556643 / 25000000000000 : ℝ))
      (E := (cell13069 ⟨6, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41930801430811 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552049556643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_7 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83826862175021 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208202219357 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨7, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83826862175021 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208202219357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_8 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83792146086983 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441641240111 / 20000000000000 : ℝ))
      (E := (cell13069 ⟨8, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83792146086983 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441641240111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_9 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83757454562401 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104105117501 / 50000000000000 : ℝ))
      (E := (cell13069 ⟨9, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83757454562401 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (1104105117501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_10 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (20930696891587 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208214213143 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨10, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (20930696891587 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208214213143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_11 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (1046101813301 / 1250000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552054564349 / 25000000000000 : ℝ))
      (E := (cell13069 ⟨11, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (1046101813301 / 1250000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552054564349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_12 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83653527021033 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (138013891101 / 6250000000000 : ℝ))
      (E := (cell13069 ⟨12, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83653527021033 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (138013891101 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_13 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (10452366675353 / 12500000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (276028284709 / 12500000000000 : ℝ))
      (E := (cell13069 ⟨13, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (10452366675353 / 12500000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (276028284709 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_14 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (5224022760953 / 6250000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441646052987 / 20000000000000 : ℝ))
      (E := (cell13069 ⟨14, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (5224022760953 / 6250000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (441646052987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_15 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (20887454826069 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (138014642677 / 6250000000000 : ℝ))
      (E := (cell13069 ⟨15, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (20887454826069 / 25000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (138014642677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_16 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41757649378029 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208238278199 / 100000000000000 : ℝ))
      (E := (cell13069 ⟨16, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41757649378029 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (2208238278199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_17 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (16696160499383 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (88329692561 / 4000000000000 : ℝ))
      (E := (cell13069 ⟨17, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (16696160499383 / 20000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (88329692561 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_18 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (41723165246673 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (276030792077 / 12500000000000 : ℝ))
      (E := (cell13069 ⟨18, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (41723165246673 / 50000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (276030792077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13069_19 : CellCertificate 13069 (876661311496063 / 10000000000000000 : ℝ) (16071798693497 / 10000000000000000 : ℝ) (81106375788239 / 2500000000000000 : ℝ)
    (cell13069 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · norm_num [cell13069]
  · have h := gap_lower (n := 13069) (a := (83411882712021 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552062587559 / 25000000000000 : ℝ))
      (E := (cell13069 ⟨19, by decide⟩).energy) (xi := (81106375788239 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13069 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13069]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13069])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13069) (a := (83411882712021 / 100000000000000 : ℝ)) (b := (6302259851 / 4000000000000 : ℝ)) (q := (552062587559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13069])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13069]

theorem cert13070_0 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (84070551255731 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208061436467 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨0, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (84070551255731 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208061436467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_1 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (84035662236383 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104032738643 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨1, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (84035662236383 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104032738643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_2 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (21000199507541 / 25000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208069460417 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨2, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (21000199507541 / 25000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208069460417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_3 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41982979300419 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (220807351 / 10000000000 : ℝ))
      (E := (cell13070 ⟨3, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41982979300419 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (220807351 / 10000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_4 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83931143912363 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (276009689793 / 12500000000000 : ℝ))
      (E := (cell13070 ⟨4, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83931143912363 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (276009689793 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_5 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41948176964443 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208081493241 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨5, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41948176964443 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208081493241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_6 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (4193079430737 / 5000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104042750109 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨6, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (4193079430737 / 5000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104042750109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_7 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (16765369586889 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (220808954663 / 10000000000000 : ℝ))
      (E := (cell13070 ⟨7, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (16765369586889 / 20000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (220808954663 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_8 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (8379213185271 / 10000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104046761757 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨8, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (8379213185271 / 10000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104046761757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_9 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (10469680041803 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104048776847 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨9, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (10469680041803 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104048776847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_10 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83722773344661 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441620305523 / 20000000000000 : ℝ))
      (E := (cell13070 ⟨10, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83722773344661 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441620305523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_11 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (41844065424339 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441621113539 / 20000000000000 : ℝ))
      (E := (cell13070 ⟨11, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (41844065424339 / 50000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441621113539 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_12 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83653512811911 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208109563789 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨12, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83653512811911 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208109563789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_13 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (10452364899997 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104056789883 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨13, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (10452364899997 / 12500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104056789883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_14 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83584349978669 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441623512599 / 20000000000000 : ℝ))
      (E := (cell13070 ⟨14, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83584349978669 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (441623512599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_15 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (2088745127849 / 2500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104060788453 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨15, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (2088745127849 / 2500000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104060788453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_16 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83515284571999 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104062813277 / 50000000000000 : ℝ))
      (E := (cell13070 ⟨16, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83515284571999 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (1104062813277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_17 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83480788319109 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208129600267 / 100000000000000 : ℝ))
      (E := (cell13070 ⟨17, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83480788319109 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (2208129600267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_18 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83446316321787 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (552033404753 / 25000000000000 : ℝ))
      (E := (cell13070 ⟨18, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83446316321787 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (552033404753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13070_19 : CellCertificate 13070 (438317434836569 / 5000000000000000 : ℝ) (1607056862973283 / 1000000000000000000 : ℝ) (32440010846887 / 1000000000000000 : ℝ)
    (cell13070 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · norm_num [cell13070]
  · have h := gap_lower (n := 13070) (a := (83411868546703 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (69004300901 / 3125000000000 : ℝ))
      (E := (cell13070 ⟨19, by decide⟩).energy) (xi := (32440010846887 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13070 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13070]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13070])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13070) (a := (83411868546703 / 100000000000000 : ℝ)) (b := (15754430243 / 10000000000000 : ℝ)) (q := (69004300901 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13070])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13070]

theorem cert13071_0 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (84070536973073 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2207948790941 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨0, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (84070536973073 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2207948790941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_1 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (42017823980033 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2207952827119 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨1, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (42017823980033 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2207952827119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_2 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (84000783760181 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (275994600707 / 12500000000000 : ℝ))
      (E := (cell13071 ⟨2, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (84000783760181 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (275994600707 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_3 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (2623935760537 / 3125000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (551990212673 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨3, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (2623935760537 / 3125000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (551990212673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_4 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (83931129655033 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441592970907 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨4, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (83931129655033 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441592970907 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_5 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41948169838937 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1103984412489 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨5, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41948169838937 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1103984412489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_6 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (83861574370039 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2207972827549 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨6, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (83861574370039 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2207972827549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_7 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (20956708424013 / 25000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2207976869601 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨7, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (20956708424013 / 25000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2207976869601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_8 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (83792117620617 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (551995210543 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨8, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (83792117620617 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (551995210543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_9 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (83757426108627 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1103992434043 / 50000000000000 : ℝ))
      (E := (cell13071 ⟨9, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (83757426108627 / 100000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (1103992434043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_10 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41861379562577 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (551997223967 / 25000000000000 : ℝ))
      (E := (cell13071 ⟨10, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41861379562577 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (551997223967 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_11 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (16737623327091 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (68999777303 / 3125000000000 : ℝ))
      (E := (cell13071 ⟨11, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (16737623327091 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (68999777303 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_12 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41826749302483 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (137999807737 / 6250000000000 : ℝ))
      (E := (cell13071 ⟨12, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41826749302483 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (137999807737 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_13 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (10452363124913 / 12500000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208000935713 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨13, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (10452363124913 / 12500000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208000935713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_14 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (10448041973033 / 12500000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441600982987 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨14, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (10448041973033 / 12500000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441600982987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_15 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41774895462909 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208008924883 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨15, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41774895462909 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208008924883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_16 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41757635195057 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441602594123 / 20000000000000 : ℝ))
      (E := (cell13071 ⟨16, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41757635195057 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (441602594123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_17 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (3339230965739 / 4000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (110400847023 / 5000000000000 : ℝ))
      (E := (cell13071 ⟨17, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (3339230965739 / 4000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (110400847023 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_18 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (41723151076199 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (276002619423 / 12500000000000 : ℝ))
      (E := (cell13071 ⟨18, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (41723151076199 / 50000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (276002619423 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13071_19 : CellCertificate 13071 (438304215861973 / 5000000000000000 : ℝ) (1606933875424143 / 1000000000000000000 : ℝ) (12974988711623 / 400000000000000 : ℝ)
    (cell13071 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · norm_num [cell13071]
  · have h := gap_lower (n := 13071) (a := (16682370876711 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208024961429 / 100000000000000 : ℝ))
      (E := (cell13071 ⟨19, by decide⟩).energy) (xi := (12974988711623 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13071 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13071]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13071])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13071) (a := (16682370876711 / 20000000000000 : ℝ)) (b := (1969151381 / 1250000000000 : ℝ)) (q := (2208024961429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13071])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13071]

theorem cert13072_0 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (42035261346301 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207836141111 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨0, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (42035261346301 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207836141111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_1 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (16807126737187 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207840172647 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨1, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (16807126737187 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207840172647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_2 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (2625024046637 / 3125000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207844146591 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨2, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (2625024046637 / 3125000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207844146591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_3 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (20991482518929 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207848187079 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨3, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (20991482518929 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207848187079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_4 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83931115399887 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207852186423 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨4, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83931115399887 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207852186423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_5 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (20974081357261 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103928105189 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨5, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (20974081357261 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103928105189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_6 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83861560127521 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103930104283 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨6, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83861560127521 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103930104283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_7 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83826819459839 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207864188273 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨7, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83826819459839 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207864188273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_8 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (16758420678141 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (551967053641 / 25000000000000 : ℝ))
      (E := (cell13072 ⟨8, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (16758420678141 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (551967053641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_9 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (5234838242813 / 6250000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103936118119 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨9, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (5234838242813 / 6250000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103936118119 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_10 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (5232671556739 / 6250000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (88315050393 / 4000000000000 : ℝ))
      (E := (cell13072 ⟨10, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (5232671556739 / 6250000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (88315050393 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_11 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83688102424409 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (68996257297 / 3125000000000 : ℝ))
      (E := (cell13072 ⟨11, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83688102424409 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (68996257297 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_12 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (41826742200099 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103942139749 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨12, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (41826742200099 / 50000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103942139749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_13 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (10452361350101 / 12500000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103944143683 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨13, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (10452361350101 / 12500000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103944143683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_14 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (16716864318407 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207892262579 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨14, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (16716864318407 / 20000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207892262579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_15 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83549776739849 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (275987033571 / 12500000000000 : ℝ))
      (E := (cell13072 ⟨15, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83549776739849 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (275987033571 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_16 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (83515256210401 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103950155193 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨16, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (83515256210401 / 100000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103950155193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_17 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (20870189992503 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103952167303 / 50000000000000 : ℝ))
      (E := (cell13072 ⟨17, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (20870189992503 / 25000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (1103952167303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_18 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (4172314399259 / 5000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207908345733 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨18, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (4172314399259 / 5000000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207908345733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13072_19 : CellCertificate 13072 (876581997647593 / 10000000000000000 : ℝ) (401702726674489 / 250000000000000000 : ℝ) (324349331117067 / 10000000000000000 : ℝ)
    (cell13072 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · norm_num [cell13072]
  · have h := gap_lower (n := 13072) (a := (5213240013911 / 6250000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207912348027 / 100000000000000 : ℝ))
      (E := (cell13072 ⟨19, by decide⟩).energy) (xi := (324349331117067 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13072 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13072]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13072])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13072) (a := (5213240013911 / 6250000000000 : ℝ)) (b := (19689990053 / 12500000000000 : ℝ)) (q := (2207912348027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13072])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13072]

theorem cert13073_0 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (84070508414319 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103861772411 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨0, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (84070508414319 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103861772411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_1 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (84035619413991 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207727513871 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨1, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (84035619413991 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207727513871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_2 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (84000755226773 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (441546308223 / 20000000000000 : ℝ))
      (E := (cell13073 ⟨2, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (84000755226773 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (441546308223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_3 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (5247869738527 / 6250000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207735577081 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨3, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (5247869738527 / 6250000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207735577081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_4 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (3357244045877 / 4000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207739571949 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨4, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (3357244045877 / 4000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207739571949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_5 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41948155591199 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (88309743659 / 4000000000000 : ℝ))
      (E := (cell13073 ⟨5, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41948155591199 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (88309743659 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_6 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (16772309177437 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103873792641 / 50000000000000 : ℝ))
      (E := (cell13073 ⟨6, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (16772309177437 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (1103873792641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_7 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (5239175326613 / 6250000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (275968952333 / 12500000000000 : ℝ))
      (E := (cell13073 ⟨7, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (5239175326613 / 6250000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (275968952333 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_8 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (20948022290743 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207755582659 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨8, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (20948022290743 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207755582659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_9 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83757397663569 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551939900023 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨9, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83757397663569 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551939900023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_10 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83722730692673 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551940904871 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨10, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83722730692673 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551940904871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_11 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83688088215539 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207767647121 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨11, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83688088215539 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207767647121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_12 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (16730694039521 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207771630911 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨12, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (16730694039521 / 20000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207771630911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_13 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83618876604487 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551943908681 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨13, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83618876604487 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551943908681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_14 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83584307401979 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (441555932821 / 20000000000000 : ℝ))
      (E := (cell13073 ⟨14, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83584307401979 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (441555932821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_15 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (41774881278027 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551945916539 / 25000000000000 : ℝ))
      (E := (cell13073 ⟨15, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (41774881278027 / 50000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (551945916539 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_16 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (4175762101643 / 5000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (441557540817 / 20000000000000 : ℝ))
      (E := (cell13073 ⟨16, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (4175762101643 / 5000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (441557540817 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_17 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (260877330621 / 312500000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207791666219 / 100000000000000 : ℝ))
      (E := (cell13073 ⟨17, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (260877330621 / 312500000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (2207791666219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_18 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (20861568455033 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (88311826941 / 4000000000000 : ℝ))
      (E := (cell13073 ⟨18, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (20861568455033 / 25000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (88311826941 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13073_19 : CellCertificate 13073 (876555567443187 / 10000000000000000 : ℝ) (803343978395201 / 500000000000000000 : ℝ) (324323948447343 / 10000000000000000 : ℝ)
    (cell13073 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · norm_num [cell13073]
  · have h := gap_lower (n := 13073) (a := (83411826063767 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (68993741573 / 3125000000000 : ℝ))
      (E := (cell13073 ⟨19, by decide⟩).energy) (xi := (324323948447343 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13073 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13073]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13073])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13073) (a := (83411826063767 / 100000000000000 : ℝ)) (b := (78753866131 / 50000000000000 : ℝ)) (q := (68993741573 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13073])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13073]

theorem cert13074_0 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (84070494138223 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207610944227 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨0, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (84070494138223 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207610944227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_1 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (84035605144233 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207614908661 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨1, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (84035605144233 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207614908661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_2 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (84000740963347 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275952366417 / 12500000000000 : ℝ))
      (E := (cell13074 ⟨2, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (84000740963347 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (275952366417 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_3 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20991475389833 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207622962781 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨3, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20991475389833 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207622962781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_4 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41965543448073 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103813476587 / 50000000000000 : ℝ))
      (E := (cell13074 ⟨4, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41965543448073 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103813476587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_5 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41948148468967 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207630968273 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨5, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41948148468967 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207630968273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_6 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (8386153164903 / 10000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207634957699 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨6, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (8386153164903 / 10000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207634957699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_7 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20956697748489 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551909746687 / 25000000000000 : ℝ))
      (E := (cell13074 ⟨7, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20956697748489 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (551909746687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_8 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (83792074937419 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207643004489 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨8, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (83792074937419 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207643004489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_9 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20939345861077 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (441529403541 / 20000000000000 : ℝ))
      (E := (cell13074 ⟨9, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20939345861077 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (441529403541 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_10 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (83722716479699 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (68989094779 / 3125000000000 : ℝ))
      (E := (cell13074 ⟨10, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (83722716479699 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (68989094779 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_11 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41844037004423 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207655056443 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨11, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41844037004423 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207655056443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_12 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (20913363999297 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207659036157 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨12, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (20913363999297 / 25000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207659036157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_13 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (4180943120517 / 5000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207663035941 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨13, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (4180943120517 / 5000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207663035941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_14 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (5224018325881 / 6250000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (110383353067 / 5000000000000 : ℝ))
      (E := (cell13074 ⟨14, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (5224018325881 / 6250000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (110383353067 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_15 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (83549748374431 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103835529727 / 50000000000000 : ℝ))
      (E := (cell13074 ⟨15, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (83549748374431 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (1103835529727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_16 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (8351522785749 / 10000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (441535018699 / 20000000000000 : ℝ))
      (E := (cell13074 ⟨16, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (8351522785749 / 10000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (441535018699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_17 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (83480731629599 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (220767911003 / 10000000000000 : ℝ))
      (E := (cell13074 ⟨17, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (83480731629599 / 100000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (220767911003 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_18 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41723129828627 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207683113563 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨18, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41723129828627 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207683113563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

theorem cert13074_19 : CellCertificate 13074 (175305828221967 / 2000000000000000 : ℝ) (1606565025697161 / 1000000000000000000 : ℝ) (324298569780401 / 10000000000000000 : ℝ)
    (cell13074 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · norm_num [cell13074]
  · have h := gap_lower (n := 13074) (a := (41705905953563 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207687108359 / 100000000000000 : ℝ))
      (E := (cell13074 ⟨19, by decide⟩).energy) (xi := (324298569780401 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13074 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13074]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13074])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13074) (a := (41705905953563 / 50000000000000 : ℝ)) (b := (78747772997 / 50000000000000 : ℝ)) (q := (2207687108359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13074])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13074]

end BstLean.Part268
