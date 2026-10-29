import BstLean.Part268CellShard29Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13075_0 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (42035239932157 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207498339329 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨0, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (42035239932157 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207498339329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_1 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (4201779543833 / 5000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207502357019 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨1, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (4201779543833 / 5000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207502357019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_2 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (16800145340421 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (44150127503 / 2000000000000 : ℝ))
      (E := (cell13075 ⟨2, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (16800145340421 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (44150127503 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_3 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (2623933978263 / 3125000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207510402097 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨3, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (2623933978263 / 3125000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207510402097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_4 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83931072647549 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (55187859701 / 2500000000000 : ℝ))
      (E := (cell13075 ⟨4, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83931072647549 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (55187859701 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_5 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83896282695651 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (137969899921 / 6250000000000 : ℝ))
      (E := (cell13075 ⟨5, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83896282695651 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (137969899921 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_6 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (1310336209579 / 1562500000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441504476761 / 20000000000000 : ℝ))
      (E := (cell13075 ⟨6, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (1310336209579 / 1562500000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441504476761 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_7 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20956694191071 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441505281709 / 20000000000000 : ℝ))
      (E := (cell13075 ⟨7, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20956694191071 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441505281709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_8 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20948015178511 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (275941302753 / 12500000000000 : ℝ))
      (E := (cell13075 ⟨8, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20948015178511 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (275941302753 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_9 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (3350294769089 / 4000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (137970901939 / 6250000000000 : ℝ))
      (E := (cell13075 ⟨9, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (3350294769089 / 4000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (137970901939 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_10 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83722702268901 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207538442079 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨10, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83722702268901 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207538442079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_11 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83688059804329 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207542461471 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨11, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83688059804329 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207542461471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_12 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (16730688359789 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (220754643711 / 10000000000000 : ℝ))
      (E := (cell13075 ⟨12, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (16730688359789 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (220754643711 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_13 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41809424109183 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207550491017 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨13, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41809424109183 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207550491017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_14 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83584279028387 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207554454283 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨14, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83584279028387 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207554454283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_15 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83549734194979 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207558506661 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨15, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83549734194979 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207558506661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_16 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20878803421073 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441512495723 / 20000000000000 : ℝ))
      (E := (cell13075 ⟨16, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20878803421073 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441512495723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_17 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (10435089682831 / 12500000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551891622827 / 25000000000000 : ℝ))
      (E := (cell13075 ⟨17, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (10435089682831 / 12500000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551891622827 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_18 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (16689249099309 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (1103785274657 / 50000000000000 : ℝ))
      (E := (cell13075 ⟨18, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (16689249099309 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (1103785274657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_19 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83411797752653 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441514908077 / 20000000000000 : ℝ))
      (E := (cell13075 ⟨19, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83411797752653 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441514908077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13076_0 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (84070465592591 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (275923223497 / 12500000000000 : ℝ))
      (E := (cell13076 ⟨0, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (84070465592591 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (275923223497 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_1 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (84035576611273 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (88295592043 / 4000000000000 : ℝ))
      (E := (cell13076 ⟨1, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (84035576611273 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (88295592043 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_2 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (10500089055381 / 12500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103696907331 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨2, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (10500089055381 / 12500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103696907331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_3 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83965873051683 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103698918557 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨3, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83965873051683 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103698918557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_4 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41965529200567 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (137962613663 / 6250000000000 : ℝ))
      (E := (cell13076 ⟨4, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41965529200567 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (137962613663 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_5 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83896268455549 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207405824901 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨5, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83896268455549 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207405824901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_6 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83861503179261 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207409863603 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨6, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83861503179261 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207409863603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_7 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (10478345317099 / 12500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103706913023 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨7, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (10478345317099 / 12500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103706913023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_8 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83792046492847 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (8622725919 / 390625000000 : ℝ))
      (E := (cell13076 ⟨8, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83792046492847 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (8622725919 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_9 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83757355012319 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103710949053 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨9, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83757355012319 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103710949053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_10 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (2093067201507 / 2500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (275928238127 / 12500000000000 : ℝ))
      (E := (cell13076 ⟨10, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (2093067201507 / 2500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (275928238127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_11 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83688045601987 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207429920311 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨11, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83688045601987 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207429920311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_12 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83653427602877 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (22074338919 / 1000000000000 : ℝ))
      (E := (cell13076 ⟨12, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83653427602877 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (22074338919 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_13 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83618834028567 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207437883651 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨13, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83618834028567 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207437883651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_14 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (1671685296897 / 2000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207441901111 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨14, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (1671685296897 / 2000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207441901111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_15 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (835497200177 / 1000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103722974789 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨15, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (835497200177 / 1000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103722974789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_16 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (5219699969579 / 6250000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207449917669 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨16, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (5219699969579 / 6250000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207449917669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_17 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83480703297867 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (137965870409 / 6250000000000 : ℝ))
      (E := (cell13076 ⟨17, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83480703297867 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (137965870409 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_18 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (16689246267601 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (110372899039 / 5000000000000 : ℝ))
      (E := (cell13076 ⟨18, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (16689246267601 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (110372899039 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_19 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83411783600349 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103730984063 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨19, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83411783600349 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103730984063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13077_0 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (84070451323053 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207273232321 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨0, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (84070451323053 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207273232321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_1 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (84035562348069 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (4311088361 / 195312500000 : ℝ))
      (E := (cell13077 ⟨1, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (84035562348069 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (4311088361 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_2 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (42000349093087 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551820312469 / 25000000000000 : ℝ))
      (E := (cell13077 ⟨2, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (42000349093087 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551820312469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_3 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (20991464700283 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (275910658479 / 12500000000000 : ℝ))
      (E := (cell13077 ⟨3, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (20991464700283 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (275910658479 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_4 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83931044156901 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103644651409 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨4, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83931044156901 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103644651409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_5 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (20974063554407 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207293304733 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨5, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (20974063554407 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207293304733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_6 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83861488947647 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441459456223 / 20000000000000 : ℝ))
      (E := (cell13077 ⟨6, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83861488947647 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441459456223 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_7 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41913374155739 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103650648631 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨7, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41913374155739 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103650648631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_8 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83792032273829 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103652651121 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨8, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83792032273829 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103652651121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_9 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83757340799589 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441461872179 / 20000000000000 : ℝ))
      (E := (cell13077 ⟨9, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83757340799589 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441461872179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_10 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (16744534770767 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207313363661 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨10, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (16744534770767 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207313363661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_11 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (4184401570091 / 5000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (110365868743 / 5000000000000 : ℝ))
      (E := (cell13077 ⟨11, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (4184401570091 / 5000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (110365868743 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_12 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83653413408983 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103660671199 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨12, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83653413408983 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103660671199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_13 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (4180940992047 / 5000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (275915673537 / 12500000000000 : ℝ))
      (E := (cell13077 ⟨13, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (4180940992047 / 5000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (275915673537 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_14 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (16716850132697 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207329401823 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨14, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (16716850132697 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207329401823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_15 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83549705842591 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207333388207 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨15, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83549705842591 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207333388207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_16 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83515185344407 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103668705327 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨16, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83515185344407 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103668705327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_17 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41740344567627 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103670707869 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨17, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41740344567627 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103670707869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_18 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83446217181633 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207345407959 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨18, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83446217181633 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207345407959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_19 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83411769450211 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103674724937 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨19, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83411769450211 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103674724937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13078_0 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (840704370557 / 1000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103580365107 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨0, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (840704370557 / 1000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103580365107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_1 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (1680710961741 / 2000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207164734159 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨1, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (1680710961741 / 2000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207164734159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_2 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (84000683931483 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (441433747737 / 20000000000000 : ℝ))
      (E := (cell13078 ⟨2, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (84000683931483 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (441433747737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_3 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83965844552763 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (220717275217 / 10000000000000 : ℝ))
      (E := (cell13078 ⟨3, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83965844552763 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (220717275217 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_4 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (1678620598297 / 2000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207176782731 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨4, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (1678620598297 / 2000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207176782731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_5 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83896239981887 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207180780269 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨5, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83896239981887 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207180780269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_6 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83861474718211 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207184810309 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨6, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83861474718211 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207184810309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_7 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (41913367044171 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (551797205549 / 25000000000000 : ℝ))
      (E := (cell13078 ⟨7, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (41913367044171 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (551797205549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_8 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83792018056987 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207192822963 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨8, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83792018056987 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207192822963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_9 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (20939331647259 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (34487450303 / 1562500000000 : ℝ))
      (E := (cell13078 ⟨9, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (20939331647259 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (34487450303 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_10 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (16744531929913 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (441440163603 / 20000000000000 : ℝ))
      (E := (cell13078 ⟨10, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (16744531929913 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (441440163603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_11 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (20922004300957 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207204825117 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨11, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (20922004300957 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207204825117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_12 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83653399217263 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103604423367 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨12, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83653399217263 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103604423367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_13 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (41809402827743 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103606444327 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨13, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (41809402827743 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103606444327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_14 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (20896059121073 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (275902112281 / 12500000000000 : ℝ))
      (E := (cell13078 ⟨14, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (20896059121073 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (275902112281 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_15 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83549691669653 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207220880747 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨15, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83549691669653 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207220880747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_16 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (41757585588859 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (551806224839 / 25000000000000 : ℝ))
      (E := (cell13078 ⟨16, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (41757585588859 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (551806224839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_17 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83480674974811 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207228900647 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨17, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83480674974811 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207228900647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_18 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (20861550756857 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207232889123 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨18, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (20861550756857 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207232889123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_19 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (521323470639 / 625000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207236927339 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨19, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (521323470639 / 625000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207236927339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13079_0 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (84070422790531 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (34485128497 / 1562500000000 : ℝ))
      (E := (cell13079 ⟨0, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (84070422790531 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (34485128497 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_1 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16807106765643 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103526140529 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨1, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16807106765643 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103526140529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_2 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (42000334839487 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207056281091 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨2, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (42000334839487 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207056281091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_3 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (5247864394161 / 6250000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207060290129 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨3, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (5247864394161 / 6250000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207060290129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_4 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41965507837489 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (44141285167 / 2000000000000 : ℝ))
      (E := (cell13079 ⟨4, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41965507837489 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (44141285167 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_5 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41948112874163 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (88282732379 / 4000000000000 : ℝ))
      (E := (cell13079 ⟨5, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41948112874163 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (88282732379 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_6 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16772292098191 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207072277221 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨6, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16772292098191 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207072277221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_7 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (10478339983423 / 12500000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103538142413 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨7, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (10478339983423 / 12500000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103538142413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_8 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41896001921161 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207080339391 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨8, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41896001921161 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207080339391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_9 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83757312380659 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441416866331 / 20000000000000 : ℝ))
      (E := (cell13079 ⟨9, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83757312380659 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441416866331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_10 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83722645447469 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207088326161 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨10, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83722645447469 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207088326161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_11 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83688003008009 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207092329191 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨11, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83688003008009 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207092329191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_12 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16730677005543 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103548173391 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨12, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16730677005543 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103548173391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_13 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83618791472203 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (88284015389 / 4000000000000 : ℝ))
      (E := (cell13079 ⟨13, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83618791472203 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (88284015389 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_14 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83584222307269 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551776097597 / 25000000000000 : ℝ))
      (E := (cell13079 ⟨14, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83584222307269 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551776097597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_15 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16709935499777 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207108369001 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨15, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16709935499777 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207108369001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_16 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83515157013199 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207112383773 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨16, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83515157013199 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207112383773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_17 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16696132163307 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207116439517 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨17, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16696132163307 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207116439517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_18 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83446188875391 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (137945026517 / 6250000000000 : ℝ))
      (E := (cell13079 ⟨18, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83446188875391 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (137945026517 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_19 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16682348231287 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103562229407 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨19, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16682348231287 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103562229407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13080_0 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (84070408527547 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206935770951 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨0, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (84070408527547 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206935770951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_1 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (42017759785781 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (220693976579 / 10000000000000 : ℝ))
      (E := (cell13080 ⟨1, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (42017759785781 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (220693976579 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_2 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (10500081928581 / 12500000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1379339887 / 62500000000 : ℝ))
      (E := (cell13080 ⟨2, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (10500081928581 / 12500000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1379339887 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_3 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83965816062571 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206947823791 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨3, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83965816062571 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206947823791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_4 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83931001437287 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103475893807 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨4, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83931001437287 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103475893807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_5 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (5243513219809 / 6250000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206955834387 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨5, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (5243513219809 / 6250000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206955834387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_6 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (20965361566469 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (275869981977 / 12500000000000 : ℝ))
      (E := (cell13080 ⟨6, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (20965361566469 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (275869981977 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_7 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (20956676412151 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (441392771837 / 20000000000000 : ℝ))
      (E := (cell13080 ⟨7, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (20956676412151 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (441392771837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_8 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41895994814917 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (275870981441 / 12500000000000 : ℝ))
      (E := (cell13080 ⟨8, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41895994814917 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (275870981441 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_9 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83757298174457 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551742959907 / 25000000000000 : ℝ))
      (E := (cell13080 ⟨9, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83757298174457 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551742959907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_10 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83722631247549 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (68967996503 / 3125000000000 : ℝ))
      (E := (cell13080 ⟨10, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83722631247549 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (68967996503 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_11 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (20921997203591 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206979887079 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨11, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (20921997203591 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206979887079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_12 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83653370840339 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206983900671 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨12, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83653370840339 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206983900671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_13 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (20904694322773 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206987876509 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨13, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (20904694322773 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2206987876509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_14 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83584208132417 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (68968498013 / 3125000000000 : ℝ))
      (E := (cell13080 ⟨14, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83584208132417 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (68968498013 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_15 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83549663330287 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (4310538889 / 195312500000 : ℝ))
      (E := (cell13080 ⟨15, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83549663330287 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (4310538889 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_16 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83515142850849 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103499961063 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨16, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83515142850849 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103499961063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_17 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83480646660427 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (110350195793 / 5000000000000 : ℝ))
      (E := (cell13080 ⟨17, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83480646660427 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (110350195793 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_18 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (1043077184069 / 1250000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103503977569 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨18, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (1043077184069 / 1250000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103503977569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_19 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (20852931753199 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207011986007 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨19, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (20852931753199 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207011986007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13081_0 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (42035197133373 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (551705828449 / 25000000000000 : ℝ))
      (E := (cell13081 ⟨0, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (42035197133373 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (551705828449 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_1 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (21008876329273 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206827361967 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨1, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (21008876329273 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206827361967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_2 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (84000641180503 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103415676507 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨2, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (84000641180503 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103415676507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_3 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (16793160364149 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206835353161 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨3, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (16793160364149 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206835353161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_4 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (5245686700111 / 6250000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (88273574821 / 4000000000000 : ℝ))
      (E := (cell13081 ⟨4, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (5245686700111 / 6250000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (88273574821 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_5 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (83896197287741 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103421677503 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨5, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (83896197287741 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103421677503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_6 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (3354457281719 / 4000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206847372131 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨6, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (3354457281719 / 4000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206847372131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_7 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (10478336429 / 12500000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206851371243 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨7, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (10478336429 / 12500000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206851371243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_8 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (83791975419521 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206855417411 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨8, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (83791975419521 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206855417411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_9 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (8375728397043 / 10000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220685940137 / 10000000000000 : ℝ))
      (E := (cell13081 ⟨9, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (8375728397043 / 10000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220685940137 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_10 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41861308524901 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441372689149 / 20000000000000 : ℝ))
      (E := (cell13081 ⟨10, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41861308524901 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441372689149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_11 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (83687974622891 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103433720341 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨11, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (83687974622891 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103433720341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_12 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (2614167395473 / 3125000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206871450273 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨12, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (2614167395473 / 3125000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206871450273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_13 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (10452345389019 / 12500000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206875480309 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨13, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (10452345389019 / 12500000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206875480309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_14 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (16716838791947 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206879478159 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨14, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (16716838791947 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206879478159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_15 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (83549649163857 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206883449053 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨15, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (83549649163857 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206883449053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_16 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41757564345333 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103443728099 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨16, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41757564345333 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103443728099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_17 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41740316253243 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220689150441 / 10000000000000 : ℝ))
      (E := (cell13081 ⟨17, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41740316253243 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220689150441 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_18 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (16689232115563 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (88275819269 / 4000000000000 : ℝ))
      (E := (cell13081 ⟨18, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (16689232115563 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (88275819269 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_19 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41705856435661 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (55172487723 / 2500000000000 : ℝ))
      (E := (cell13081 ⟨19, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41705856435661 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (55172487723 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13082_0 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (1313599687627 / 1562500000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (137919431887 / 6250000000000 : ℝ))
      (E := (cell13082 ⟨0, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (1313599687627 / 1562500000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (137919431887 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_1 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (21008872766201 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103357447989 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨1, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (21008872766201 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103357447989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_2 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (84000626934539 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206718940427 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨2, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (84000626934539 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206718940427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_3 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (839657875811 / 1000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (275840367019 / 12500000000000 : ℝ))
      (E := (cell13082 ⟨3, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (839657875811 / 1000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (275840367019 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_4 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83930972968443 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206726949143 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨4, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83930972968443 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206726949143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_5 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20974045765179 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206730929297 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨5, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20974045765179 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206730929297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_6 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83861417822251 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206734942143 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨6, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83861417822251 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206734942143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_7 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20956669304393 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206738937021 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨7, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20956669304393 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206738937021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_8 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83791961211383 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206742979003 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨8, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83791961211383 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206742979003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_9 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83757269768577 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206746958823 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨9, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83757269768577 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206746958823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_10 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20930650713557 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103375499553 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨10, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20930650713557 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103375499553 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_11 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83687960433591 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206754989997 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨11, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83687960433591 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206754989997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_12 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (10456667809013 / 12500000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206758995589 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨12, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (10456667809013 / 12500000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206758995589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_13 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83618748935383 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206763021673 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨13, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83618748935383 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206763021673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_14 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83584179789223 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103383507809 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨14, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83584179789223 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103383507809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_15 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20887408749899 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206771040851 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨15, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20887408749899 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206771040851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_16 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83515114532651 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (137923440263 / 6250000000000 : ℝ))
      (E := (cell13082 ⟨16, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83515114532651 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (137923440263 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_17 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (10435077294339 / 12500000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103389544339 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨17, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (10435077294339 / 12500000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103389544339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_18 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20861536608069 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103391531149 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨18, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20861536608069 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103391531149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_19 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83411698732013 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551696771461 / 25000000000000 : ℝ))
      (E := (cell13082 ⟨19, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83411698732013 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551696771461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13083_0 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (21017591437923 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (441319700459 / 20000000000000 : ℝ))
      (E := (cell13083 ⟨0, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (21017591437923 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (441319700459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_1 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (84035476814697 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103301241783 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨1, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (84035476814697 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103301241783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_2 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (21000153172689 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551651630887 / 25000000000000 : ℝ))
      (E := (cell13083 ⟨2, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (21000153172689 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551651630887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_3 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41982886671817 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103305257427 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨3, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41982886671817 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103305257427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_4 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83930958737289 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (137913407717 / 6250000000000 : ℝ))
      (E := (cell13083 ⟨4, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83930958737289 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (137913407717 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_5 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (20974042208967 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (137913659829 / 6250000000000 : ℝ))
      (E := (cell13083 ⟨5, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (20974042208967 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (137913659829 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_6 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (10482675450463 / 12500000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206622565853 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨6, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (10482675450463 / 12500000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206622565853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_7 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83826663005319 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551656639131 / 25000000000000 : ℝ))
      (E := (cell13083 ⟨7, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83826663005319 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551656639131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_8 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (4189597350271 / 5000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206630594343 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨8, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (4189597350271 / 5000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206630594343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_9 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41878627784449 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (34478665157 / 1562500000000 : ℝ))
      (E := (cell13083 ⟨9, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41878627784449 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (34478665157 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_10 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83722588660827 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206638606263 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨10, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83722588660827 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206638606263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_11 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83687946246463 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551660648283 / 25000000000000 : ℝ))
      (E := (cell13083 ⟨11, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83687946246463 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551660648283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_12 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41826664145621 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206646594751 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨12, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41826664145621 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206646594751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_13 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83618734760783 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206650616907 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨13, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83618734760783 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206650616907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_14 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83584165620879 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (220665460697 / 10000000000000 : ℝ))
      (E := (cell13083 ⟨14, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83584165620879 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (220665460697 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_15 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83549620837503 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206658628369 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨15, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83549620837503 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206658628369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_16 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83515100376803 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206662627939 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨16, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83515100376803 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206662627939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_17 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (5217537762819 / 6250000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206666668667 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨17, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (5217537762819 / 6250000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206666668667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_18 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41723066144451 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206670696861 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨18, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41723066144451 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206670696861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_19 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (20852921148717 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551668664623 / 25000000000000 : ℝ))
      (E := (cell13083 ⟨19, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (20852921148717 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551668664623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13084_0 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (42035175748719 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206486090103 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨0, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (42035175748719 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206486090103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_1 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (21008865641693 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206490124731 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨1, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (21008865641693 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206490124731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_2 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82031834423 / 97656250000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206494102377 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨2, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82031834423 / 97656250000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206494102377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_3 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83965759108347 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206498147181 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨3, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83965759108347 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206498147181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_4 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83930944508313 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (44130043029 / 2000000000000 : ℝ))
      (E := (cell13084 ⟨4, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83930944508313 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (44130043029 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_5 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83896154613197 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (110325309047 / 5000000000000 : ℝ))
      (E := (cell13084 ⟨5, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83896154613197 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (110325309047 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_6 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83861389387333 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103255092637 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨6, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83861389387333 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103255092637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_7 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83826648795243 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (275814271467 / 12500000000000 : ℝ))
      (E := (cell13084 ⟨7, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83826648795243 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (275814271467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_8 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (2618497900051 / 3125000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441303641079 / 20000000000000 : ℝ))
      (E := (cell13084 ⟨8, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (2618497900051 / 3125000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441303641079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_9 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (327176724107 / 390625000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103261088493 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨9, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (327176724107 / 390625000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103261088493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_10 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41861287234799 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103263104567 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨10, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41861287234799 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103263104567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_11 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41843966030753 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206530191983 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨11, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41843966030753 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206530191983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_12 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (10456664264069 / 12500000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441306849551 / 20000000000000 : ℝ))
      (E := (cell13084 ⟨12, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (10456664264069 / 12500000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441306849551 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_13 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83618720588353 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206538207857 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨13, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83618720588353 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206538207857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_14 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (5224009465919 / 6250000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441308450443 / 20000000000000 : ℝ))
      (E := (cell13084 ⟨14, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (5224009465919 / 6250000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441308450443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_15 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83549606677577 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551636567451 / 25000000000000 : ℝ))
      (E := (cell13084 ⟨15, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83549606677577 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551636567451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_16 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41757543111561 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (220655026561 / 10000000000000 : ℝ))
      (E := (cell13084 ⟨16, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41757543111561 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (220655026561 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_17 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83480590057661 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206554302623 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨17, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83480590057661 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206554302623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_18 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83446118147693 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103279134439 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨18, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83446118147693 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103279134439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_19 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83411670459887 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206562285153 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨19, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83411670459887 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206562285153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13085_0 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (42035168622683 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103186865733 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨0, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (42035168622683 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103186865733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_1 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (84035448321027 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (551594440401 / 25000000000000 : ℝ))
      (E := (cell13085 ⟨1, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (84035448321027 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (551594440401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_2 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (84000584209729 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103190896351 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨2, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (84000584209729 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103190896351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_3 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83965744875239 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206385775217 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨3, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83965744875239 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206385775217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_4 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (16786186056303 / 20000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103194887569 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨4, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (16786186056303 / 20000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103194887569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_5 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83896140392703 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206393800329 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨5, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83896140392703 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206393800329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_6 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (41930687586569 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (275799725051 / 12500000000000 : ℝ))
      (E := (cell13085 ⟨6, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (41930687586569 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (275799725051 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_7 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (4191331729367 / 5000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (275800222833 / 12500000000000 : ℝ))
      (E := (cell13085 ⟨7, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (4191331729367 / 5000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (275800222833 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_8 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83791918600017 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103202906081 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨8, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83791918600017 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103202906081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_9 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83757227176059 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103204918849 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨9, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83757227176059 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103204918849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_10 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83722560280541 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206413865803 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨10, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83722560280541 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206413865803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_11 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (261524743371 / 312500000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (441283568931 / 20000000000000 : ℝ))
      (E := (cell13085 ⟨11, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (261524743371 / 312500000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (441283568931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_12 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83653299936031 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (44128436767 / 2000000000000 : ℝ))
      (E := (cell13085 ⟨12, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83653299936031 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (44128436767 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_13 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83618706418091 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103212926339 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨13, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83618706418091 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103212926339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_14 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83584137290697 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (110321494659 / 5000000000000 : ℝ))
      (E := (cell13085 ⟨14, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83584137290697 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (110321494659 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_15 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83549592519819 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (27580423837 / 1250000000000 : ℝ))
      (E := (cell13085 ⟨15, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83549592519819 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (27580423837 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_16 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83515072071607 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206437899003 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨16, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83515072071607 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206437899003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_17 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (1304383998631 / 1562500000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (22064419323 / 1000000000000 : ℝ))
      (E := (cell13085 ⟨17, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (1304383998631 / 1562500000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (22064419323 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_18 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (10430763001081 / 12500000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103222976577 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨18, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (10430763001081 / 12500000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103222976577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_19 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83411656327069 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206449965831 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨19, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83411656327069 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206449965831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13086_0 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (3362812919819 / 4000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (137891339149 / 6250000000000 : ℝ))
      (E := (cell13086 ⟨0, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (3362812919819 / 4000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (137891339149 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_1 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (84035434077461 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551566348547 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨1, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (84035434077461 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551566348547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_2 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (21000142493121 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551567355211 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨2, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (21000142493121 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551567355211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_3 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83965730644309 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206273456883 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨3, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83965730644309 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206273456883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_4 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41965458028447 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (6894617039 / 312500000000 : ℝ))
      (E := (cell13086 ⟨4, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41965458028447 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (6894617039 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_5 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41948063087193 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206281473393 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨5, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41948063087193 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206281473393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_6 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41930680480559 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551571367311 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨6, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41930680480559 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551571367311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_7 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20956655095403 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206289447317 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨7, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20956655095403 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206289447317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_8 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (3351676176023 / 4000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (55157336817 / 2500000000000 : ℝ))
      (E := (cell13086 ⟨8, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (3351676176023 / 4000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (55157336817 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_9 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83757212982899 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (17650379953 / 800000000000 : ℝ))
      (E := (cell13086 ⟨9, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83757212982899 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (17650379953 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_10 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (10465318261707 / 12500000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551575379547 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨10, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (10465318261707 / 12500000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551575379547 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_11 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (10460987962263 / 12500000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103152746523 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨11, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (10460987962263 / 12500000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103152746523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_12 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83653285761679 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206309540921 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨12, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83653285761679 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206309540921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_13 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41809346124999 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (220631355137 / 10000000000000 : ℝ))
      (E := (cell13086 ⟨13, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41809346124999 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (220631355137 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_14 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83584123128857 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (441263505973 / 20000000000000 : ℝ))
      (E := (cell13086 ⟨14, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83584123128857 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (441263505973 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_15 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83549578364227 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206321539837 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨15, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83549578364227 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206321539837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_16 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83515057922257 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206325586341 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨16, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83515057922257 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206325586341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_17 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83480561769271 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206329557701 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨17, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83480561769271 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206329557701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_18 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83446089871767 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206333574887 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨18, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83446089871767 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206333574887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_19 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41705821098207 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206337583941 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨19, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41705821098207 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206337583941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13087_0 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (21017577186941 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441229811833 / 20000000000000 : ℝ))
      (E := (cell13087 ⟨0, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (21017577186941 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441229811833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_1 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (21008854959019 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (68942283761 / 3125000000000 : ℝ))
      (E := (cell13087 ⟨1, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (21008854959019 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (68942283761 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_2 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (42000277868709 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (4308900591 / 195312500000 : ℝ))
      (E := (cell13087 ⟨2, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (42000277868709 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (4308900591 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_3 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83965716415557 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (110308056713 / 5000000000000 : ℝ))
      (E := (cell13087 ⟨3, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83965716415557 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (110308056713 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_4 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (1678618036689 / 2000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441233025107 / 20000000000000 : ℝ))
      (E := (cell13087 ⟨4, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (1678618036689 / 2000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441233025107 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_5 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83896111958243 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206169142173 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨5, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83896111958243 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206169142173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_6 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (10482668343909 / 12500000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441234626759 / 20000000000000 : ℝ))
      (E := (cell13087 ⟨6, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (10482668343909 / 12500000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441234626759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_7 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41913303089029 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206177165697 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨7, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41913303089029 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206177165697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_8 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41895945101653 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (551545296737 / 25000000000000 : ℝ))
      (E := (cell13087 ⟨8, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41895945101653 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (551545296737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_9 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (8375719879191 / 10000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206185146271 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨9, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (8375719879191 / 10000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206185146271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_10 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83722531908941 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206189166293 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨10, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83722531908941 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206189166293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_11 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41843944759829 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206193195261 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨11, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41843944759829 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206193195261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_12 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (10456658948687 / 12500000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (551549295271 / 25000000000000 : ℝ))
      (E := (cell13087 ⟨12, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (10456658948687 / 12500000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (551549295271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_13 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41809339042037 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206201187631 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨13, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41809339042037 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206201187631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_14 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (2612003405287 / 3125000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (68943913139 / 3125000000000 : ℝ))
      (E := (cell13087 ⟨14, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (2612003405287 / 3125000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (68943913139 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_15 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83549564210801 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (551552306659 / 25000000000000 : ℝ))
      (E := (cell13087 ⟨15, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83549564210801 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (551552306659 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_16 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83515043775073 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103106634701 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨16, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83515043775073 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103106634701 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_17 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83480547628323 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206217237071 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨17, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83480547628323 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206217237071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_18 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (10430759467131 / 12500000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441244250123 / 20000000000000 : ℝ))
      (E := (cell13087 ⟨18, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (10430759467131 / 12500000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441244250123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_19 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (1042645350849 / 1250000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (275778157009 / 12500000000000 : ℝ))
      (E := (cell13087 ⟨19, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (1042645350849 / 1250000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (275778157009 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13088_0 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (84070294502233 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206036803351 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨0, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (84070294502233 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206036803351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_1 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (84035405596869 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103020410049 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨1, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (84035405596869 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103020410049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_2 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (8400054150453 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206044780051 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨2, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (8400054150453 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206044780051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_3 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83965702188981 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206048807351 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨3, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83965702188981 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206048807351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_4 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83930887614181 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (34469574911 / 1562500000000 : ℝ))
      (E := (cell13088 ⟨4, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83930887614181 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (34469574911 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_5 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (20974024436069 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206056806667 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨5, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (20974024436069 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206056806667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_6 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83861332543601 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (137878803253 / 6250000000000 : ℝ))
      (E := (cell13088 ⟨6, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83861332543601 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (137878803253 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_7 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83826591976677 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (137879054987 / 6250000000000 : ℝ))
      (E := (cell13088 ⟨7, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83826591976677 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (137879054987 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_8 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (8379187600821 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103034419449 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨8, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (8379187600821 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103034419449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_9 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (20939296150773 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206072852193 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨9, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (20939296150773 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206072852193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_10 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83722517726397 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206076868197 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨10, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83722517726397 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206076868197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_11 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83687875343381 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (551520223299 / 25000000000000 : ℝ))
      (E := (cell13088 ⟨11, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83687875343381 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (551520223299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_12 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41826628709741 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441216975019 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨12, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41826628709741 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441216975019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_13 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (20904665980079 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206088935917 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨13, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (20904665980079 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206088935917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_14 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41792047405839 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206092906753 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨14, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41792047405839 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206092906753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_15 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83549550059541 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206096909157 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨15, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83549550059541 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206096909157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_16 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83515029630053 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206100948187 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨16, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83515029630053 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206100948187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_17 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41740266744769 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (551526242603 / 25000000000000 : ℝ))
      (E := (cell13088 ⟨17, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41740266744769 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (551526242603 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_18 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83446061604493 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441221796067 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨18, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83446061604493 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441221796067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_19 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83411613941589 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206112982219 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨19, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83411613941589 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206112982219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13089_0 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (42035140129441 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205924485401 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨0, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (42035140129441 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205924485401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_1 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (84035391359841 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102964248843 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨1, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (84035391359841 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102964248843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_2 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (84000527273819 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102966255559 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨2, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (84000527273819 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102966255559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_3 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41982843982291 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102968267037 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨3, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41982843982291 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102968267037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_4 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (83930873396089 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205940574669 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨4, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (83930873396089 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205940574669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_5 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20974020883121 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441188916561 / 20000000000000 : ℝ))
      (E := (cell13089 ⟨5, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20974020883121 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441188916561 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_6 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (10482664792263 / 12500000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102974283009 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨6, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (10482664792263 / 12500000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102974283009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_7 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20956644444367 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205952589607 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨7, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20956644444367 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205952589607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_8 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (16758372363057 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205956602637 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨8, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (16758372363057 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205956602637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_9 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (16751434083289 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (551490152973 / 25000000000000 : ℝ))
      (E := (cell13089 ⟨9, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (16751434083289 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (551490152973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_10 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41861251773011 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441192924781 / 20000000000000 : ℝ))
      (E := (cell13089 ⟨10, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41861251773011 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441192924781 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_11 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41843930584637 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (551492161239 / 25000000000000 : ℝ))
      (E := (cell13089 ⟨11, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41843930584637 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (551492161239 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_12 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20913310812909 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (551493155739 / 25000000000000 : ℝ))
      (E := (cell13089 ⟨12, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20913310812909 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (551493155739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_13 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41809324879363 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (88239064871 / 4000000000000 : ℝ))
      (E := (cell13089 ⟨13, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41809324879363 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (88239064871 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_14 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41792040328169 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205980646957 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨14, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41792040328169 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2205980646957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_15 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41774767955223 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102992322801 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨15, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41774767955223 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1102992322801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_16 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (83515015487197 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (55149717023 / 2500000000000 : ℝ))
      (E := (cell13089 ⟨16, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (83515015487197 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (55149717023 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_17 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20870129838229 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (55149817487 / 2500000000000 : ℝ))
      (E := (cell13089 ⟨17, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20870129838229 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (55149817487 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_18 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (83446047474099 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441199341157 / 20000000000000 : ℝ))
      (E := (cell13089 ⟨18, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (83446047474099 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441199341157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_19 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (83411599817419 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (68937522003 / 3125000000000 : ℝ))
      (E := (cell13089 ⟨19, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (83411599817419 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (68937522003 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13090_0 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (8407026601771 / 10000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205812278857 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨0, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (8407026601771 / 10000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205812278857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_1 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (84035377124991 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205816286729 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨1, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (84035377124991 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205816286729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_2 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (16800102609057 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102910147897 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨2, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (16800102609057 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102910147897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_3 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (2099141843559 / 2500000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (220582425651 / 10000000000000 : ℝ))
      (E := (cell13090 ⟨3, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (2099141843559 / 2500000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (220582425651 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_4 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83930859180171 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (220582829281 / 10000000000000 : ℝ))
      (E := (cell13090 ⟨4, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83930859180171 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (220582829281 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_5 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41948034661433 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (275729037087 / 12500000000000 : ℝ))
      (E := (cell13090 ⟨5, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41948034661433 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (275729037087 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_6 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83861304134779 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441167266739 / 20000000000000 : ℝ))
      (E := (cell13090 ⟨6, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83861304134779 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441167266739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_7 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (5239160223777 / 6250000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205840295139 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨7, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (5239160223777 / 6250000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205840295139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_8 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83791847624531 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205844304061 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨8, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83791847624531 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205844304061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_9 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (2617411132249 / 3125000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (137865522957 / 6250000000000 : ℝ))
      (E := (cell13090 ⟨9, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (2617411132249 / 3125000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (137865522957 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_10 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83722489367817 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551463093833 / 25000000000000 : ℝ))
      (E := (cell13090 ⟨10, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83722489367817 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551463093833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_11 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41843923498667 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102928167167 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨11, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41843923498667 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102928167167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_12 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83653229085957 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205860366541 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨12, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83653229085957 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205860366541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_13 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41809317799651 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551466090377 / 25000000000000 : ℝ))
      (E := (cell13090 ⟨13, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41809317799651 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551466090377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_14 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83584066503163 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441173676577 / 20000000000000 : ℝ))
      (E := (cell13090 ⟨14, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83584066503163 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441173676577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_15 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (16709904352703 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205872377773 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨15, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (16709904352703 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205872377773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_16 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (16703000269301 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205876409379 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨16, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (16703000269301 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205876409379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_17 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (10435063152307 / 12500000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (88235216971 / 4000000000000 : ℝ))
      (E := (cell13090 ⟨17, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (10435063152307 / 12500000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (88235216971 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_18 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (20861508336467 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205884426961 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨18, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (20861508336467 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205884426961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_19 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83411585695409 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102944210851 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨19, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83411585695409 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102944210851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13091_0 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (21017562944679 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205700010181 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨0, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (21017562944679 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205700010181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_1 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (42017681446159 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441140802723 / 20000000000000 : ℝ))
      (E := (cell13091 ⟨1, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (42017681446159 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441140802723 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_2 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (5250031176183 / 6250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (220570801829 / 10000000000000 : ℝ))
      (E := (cell13091 ⟨2, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (5250031176183 / 6250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (220570801829 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_3 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (10495707440289 / 12500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102856016291 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨3, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (10495707440289 / 12500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102856016291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_4 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20982711241607 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205716064609 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨4, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20982711241607 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205716064609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_5 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83896055115421 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (220572006427 / 10000000000000 : ℝ))
      (E := (cell13091 ⟨5, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83896055115421 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (220572006427 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_6 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83861289933627 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205724097091 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨6, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83861289933627 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205724097091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_7 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (2619579668299 / 3125000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102864056207 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨7, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (2619579668299 / 3125000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102864056207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_8 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20947958358987 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (88229284691 / 4000000000000 : ℝ))
      (E := (cell13091 ⟨8, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20947958358987 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (88229284691 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_9 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83757142049661 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102868059227 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨9, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83757142049661 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102868059227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_10 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83722475191781 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102870061241 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨10, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83722475191781 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102870061241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_11 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83687832827563 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102872067823 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨11, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83687832827563 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102872067823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_12 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (16730642984489 / 20000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102874081989 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨12, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (16730642984489 / 20000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102874081989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_13 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83618621442043 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205752155119 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨13, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83618621442043 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205752155119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_14 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41792026176077 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441151234543 / 20000000000000 : ℝ))
      (E := (cell13091 ⟨14, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41792026176077 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441151234543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_15 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20887376904687 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205760163869 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨15, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20887376904687 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205760163869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_16 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (3340599488319 / 4000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205764191789 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨16, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (3340599488319 / 4000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205764191789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_17 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83480491086159 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551442050761 / 25000000000000 : ℝ))
      (E := (cell13091 ⟨17, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83480491086159 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551442050761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_18 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83446019219797 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205772202137 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨18, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83446019219797 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205772202137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_19 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (2085289289389 / 2500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (220577619333 / 10000000000000 : ℝ))
      (E := (cell13091 ⟨19, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (2085289289389 / 2500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (220577619333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13092_0 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (840702375419 / 1000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102793897533 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨0, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (840702375419 / 1000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102793897533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_1 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (84035348661823 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205591794087 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨1, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (84035348661823 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205591794087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_2 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (84000484594747 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551398963073 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨2, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (84000484594747 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551398963073 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_3 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (2099141132611 / 2500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205599862289 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨3, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (2099141132611 / 2500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205599862289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_4 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83930830754859 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102801916063 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨4, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83930830754859 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102801916063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_5 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (1677920818203 / 2000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205607827561 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨5, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (1677920818203 / 2000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205607827561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_6 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (10482659466831 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551402964051 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨6, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (10482659466831 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551402964051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_7 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41913267596437 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102807933699 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨7, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41913267596437 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102807933699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_8 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (654623587887 / 781250000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102809934087 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨8, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (654623587887 / 781250000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102809934087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_9 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (20939281967381 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551405966329 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨9, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (20939281967381 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551405966329 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_10 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83722461017913 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205627923437 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨10, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83722461017913 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205627923437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_11 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83687818659959 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205631932681 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨11, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83687818659959 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205631932681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_12 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83653200761099 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551408974753 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨12, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83653200761099 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551408974753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_13 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83618607286951 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102819972227 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨13, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83618607286951 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102819972227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_14 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (20896009550827 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1076974589 / 48828125000 : ℝ))
      (E := (cell13092 ⟨14, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (20896009550827 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1076974589 / 48828125000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_15 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (16709898695229 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205647945693 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨15, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (16709898695229 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205647945693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_16 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83514973071609 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102825984963 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨16, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83514973071609 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102825984963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_17 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (10435059619503 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205655977541 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨17, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (10435059619503 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205655977541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_18 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83446005095887 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102829986521 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨18, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83446005095887 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102829986521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_19 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83411557457871 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205664018981 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨19, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83411557457871 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205664018981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13093_0 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (84070223307261 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205475633517 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨0, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (84070223307261 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205475633517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_1 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (2626104201047 / 3125000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551369907037 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨1, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (2626104201047 / 3125000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551369907037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_2 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (42000235186371 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551370906029 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨2, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (42000235186371 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551370906029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_3 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (41982815544371 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551371907449 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨3, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (41982815544371 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551371907449 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_4 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83930816545463 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (275686456663 / 12500000000000 : ℝ))
      (E := (cell13093 ⟨4, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83930816545463 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (275686456663 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_5 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83896026707051 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (110274782227 / 5000000000000 : ℝ))
      (E := (cell13093 ⟨5, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83896026707051 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (110274782227 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_6 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (1048265769223 / 1250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205499669029 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨6, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (1048265769223 / 1250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205499669029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_7 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (5239157562647 / 6250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551375919029 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨7, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (5239157562647 / 6250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551375919029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_8 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83791805065293 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205507672833 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨8, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83791805065293 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205507672833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_9 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (16751422738311 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205511724021 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨9, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (16751422738311 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205511724021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_10 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83722446846213 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205515720117 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨10, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83722446846213 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205515720117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_11 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (41843902247261 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102759862721 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨11, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (41843902247261 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102759862721 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_12 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (261416208131 / 312500000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205523746029 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨12, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (261416208131 / 312500000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205523746029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_13 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83618593134023 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102763864759 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨13, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83618593134023 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102763864759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_14 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83584024056627 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205531739557 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨14, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83584024056627 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205531739557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_15 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (16709895867141 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (441107156289 / 20000000000000 : ℝ))
      (E := (cell13093 ⟨15, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (16709895867141 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (441107156289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_16 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (20878739734351 / 25000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205539802017 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨16, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (20878739734351 / 25000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205539802017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_17 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83480462828049 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205543806017 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨17, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83480462828049 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205543806017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_18 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (41722995487069 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551386949487 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨18, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (41722995487069 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551386949487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_19 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (4170577167117 / 5000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205551840367 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨19, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (4170577167117 / 5000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205551840367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13094_0 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (210175522687 / 250000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102681733841 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨0, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (210175522687 / 250000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102681733841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_1 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (8206574239 / 9765625000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205367457927 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨1, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (8206574239 / 9765625000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205367457927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_2 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (84000456152911 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102685724777 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨2, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (84000456152911 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102685724777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_3 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83965616875219 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (110268772547 / 5000000000000 : ℝ))
      (E := (cell13094 ⟨3, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83965616875219 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (110268772547 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_4 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83930802338241 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102689735101 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨4, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83930802338241 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102689735101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_5 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (20974003126531 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205383515203 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨5, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (20974003126531 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205383515203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_6 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83861247343203 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (88215499103 / 4000000000000 : ℝ))
      (E := (cell13094 ⟨6, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83861247343203 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (88215499103 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_7 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83826506813999 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (275673942321 / 12500000000000 : ℝ))
      (E := (cell13094 ⟨7, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83826506813999 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (275673942321 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_8 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83791790883219 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (70572657 / 3200000000 : ℝ))
      (E := (cell13094 ⟨8, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83791790883219 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (70572657 / 3200000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_9 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (16751419903151 / 20000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (220539952039 / 10000000000000 : ℝ))
      (E := (cell13094 ⟨9, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (16751419903151 / 20000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (220539952039 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_10 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (2093060816917 / 2500000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551350892651 / 25000000000000 : ℝ))
      (E := (cell13094 ⟨10, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (2093060816917 / 2500000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551350892651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_11 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83687790331251 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102703786017 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨11, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83687790331251 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102703786017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_12 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (16730634488981 / 20000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (88216463551 / 4000000000000 : ℝ))
      (E := (cell13094 ⟨12, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (16730634488981 / 20000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (88216463551 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_13 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (4180928949163 / 5000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102707784231 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨13, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (4180928949163 / 5000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102707784231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_14 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (8358400991211 / 10000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441083914949 / 20000000000000 : ℝ))
      (E := (cell13094 ⟨14, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (8358400991211 / 10000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441083914949 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_15 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83549465197427 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102711806463 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨15, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83549465197427 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102711806463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_16 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83514944805361 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102713814919 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨16, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83514944805361 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102713814919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_17 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (20870112175559 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205431630223 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨17, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (20870112175559 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205431630223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_18 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (20861494213637 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205435618587 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨18, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (20861494213637 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205435618587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_19 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83411529228969 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551359914371 / 25000000000000 : ℝ))
      (E := (cell13094 ⟨19, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83411529228969 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551359914371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13095_0 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16814038968903 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (441050259513 / 20000000000000 : ℝ))
      (E := (cell13095 ⟨0, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16814038968903 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (441050259513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_1 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (84035305983393 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205255283423 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨1, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (84035305983393 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205255283423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_2 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16800088387051 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102629664303 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨2, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16800088387051 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102629664303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_3 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83965602663869 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102631662861 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨3, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83965602663869 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102631662861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_4 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83930788133191 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205267340763 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨4, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83930788133191 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205267340763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_5 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83895998307369 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205271323623 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨5, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83895998307369 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205271323623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_6 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83861233150737 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275659417479 / 12500000000000 : ℝ))
      (E := (cell13095 ⟨6, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83861233150737 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275659417479 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_7 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83826492627817 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551319834683 / 25000000000000 : ℝ))
      (E := (cell13095 ⟨7, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83826492627817 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551319834683 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_8 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41895888351657 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (137830211587 / 6250000000000 : ℝ))
      (E := (cell13095 ⟨8, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41895888351657 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (137830211587 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_9 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41878542671061 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (441057474109 / 20000000000000 : ℝ))
      (E := (cell13095 ⟨9, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41878542671061 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (441057474109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_10 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41861209254657 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102645708409 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨10, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41861209254657 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102645708409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_11 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41843888085073 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102647707177 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨11, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41843888085073 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102647707177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_12 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (10456644786257 / 12500000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205299427247 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨12, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (10456644786257 / 12500000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205299427247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_13 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83618564834661 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102651701567 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨13, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83618564834661 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102651701567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_14 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16716799153951 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (13783171649 / 625000000000 : ℝ))
      (E := (cell13095 ⟨14, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16716799153951 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (13783171649 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_15 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (1305460172833 / 1562500000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102655720069 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨15, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (1305460172833 / 1562500000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102655720069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_16 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83514930675479 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (220531545339 / 10000000000000 : ℝ))
      (E := (cell13095 ⟨16, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83514930675479 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (220531545339 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_17 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41740217289291 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102659725081 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨17, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41740217289291 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102659725081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_18 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83445962737117 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551330873307 / 25000000000000 : ℝ))
      (E := (cell13095 ⟨18, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83445962737117 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551330873307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_19 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (20852878779439 / 25000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (8614560431 / 390625000000 : ℝ))
      (E := (cell13095 ⟨19, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (20852878779439 / 25000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (8614560431 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13096_0 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (42035090308203 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (275642397627 / 12500000000000 : ℝ))
      (E := (cell13096 ⟨0, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (42035090308203 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (275642397627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_1 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (52522057351 / 62500000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (137821447657 / 6250000000000 : ℝ))
      (E := (cell13096 ⟨1, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (52522057351 / 62500000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (137821447657 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_2 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (84000427719773 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205147203379 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨2, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (84000427719773 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205147203379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_3 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (20991397113673 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205151196227 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨3, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (20991397113673 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205151196227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_4 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41965386965157 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (441031041409 / 20000000000000 : ℝ))
      (E := (cell13096 ⟨4, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41965386965157 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (441031041409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_5 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (16779196822157 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102579621849 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨5, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (16779196822157 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102579621849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_6 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83861218960441 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205163255803 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨6, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83861218960441 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205163255803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_7 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83826478443803 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102583625323 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨7, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83826478443803 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102583625323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_8 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41895881262789 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205171235259 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨8, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41895881262789 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205171235259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_9 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83757071170657 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (551293818621 / 25000000000000 : ℝ))
      (E := (cell13096 ⟨9, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83757071170657 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (551293818621 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_10 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41861202172057 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (55129481469 / 2500000000000 : ℝ))
      (E := (cell13096 ⟨10, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41861202172057 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (55129481469 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_11 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41843881005603 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205183252403 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨11, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41843881005603 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205183252403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_12 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83653144137371 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (44103745229 / 2000000000000 : ℝ))
      (E := (cell13096 ⟨12, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83653144137371 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (44103745229 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_13 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (3344742027529 / 4000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205191291689 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨13, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (3344742027529 / 4000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205191291689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_14 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83583981629563 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205195290491 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨14, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83583981629563 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205195290491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_15 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41774718463679 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102599660641 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨15, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41774718463679 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102599660641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_16 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41757458273879 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102601665449 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨16, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41757458273879 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102601665449 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_17 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (652190784821 / 781250000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205207324081 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨17, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (652190784821 / 781250000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205207324081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_18 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (16689189724369 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (441042272721 / 20000000000000 : ℝ))
      (E := (cell13096 ⟨18, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (16689189724369 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (441042272721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_19 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (834115010087 / 1000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205215395509 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨19, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (834115010087 / 1000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205215395509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13097_0 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (10508770798809 / 12500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (441005412037 / 20000000000000 : ℝ))
      (E := (cell13097 ⟨0, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (10508770798809 / 12500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (441005412037 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_1 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (42017638770991 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205031095191 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨1, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (42017638770991 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205031095191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_2 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (16800082701293 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (137814692117 / 6250000000000 : ℝ))
      (E := (cell13097 ⟨2, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (16800082701293 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (137814692117 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_3 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (10495696780961 / 12500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205039120371 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨3, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (10495696780961 / 12500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205039120371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_4 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (10491344966201 / 12500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205043126993 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨4, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (10491344966201 / 12500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205043126993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_5 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (20973992479093 / 25000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (220504710153 / 10000000000000 : ℝ))
      (E := (cell13097 ⟨5, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (20973992479093 / 25000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (220504710153 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_6 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (16772240954463 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (551262777377 / 25000000000000 : ℝ))
      (E := (cell13097 ⟨6, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (16772240954463 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (551262777377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_7 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41913232130979 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (551263789571 / 25000000000000 : ℝ))
      (E := (cell13097 ⟨7, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41913232130979 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (551263789571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_8 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83791748350009 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (275632392361 / 12500000000000 : ℝ))
      (E := (cell13097 ⟨8, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83791748350009 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (275632392361 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_9 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41878528500679 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (275632896769 / 12500000000000 : ℝ))
      (E := (cell13097 ⟨9, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41878528500679 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (275632896769 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_10 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (2093059754527 / 2500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205067154511 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨10, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (2093059754527 / 2500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205067154511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_11 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (2615242120451 / 3125000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205071202391 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨11, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (2615242120451 / 3125000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205071202391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_12 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (1673062599737 / 2000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205075207639 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨12, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (1673062599737 / 2000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205075207639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_13 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (5226158533997 / 6250000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (88203167039 / 4000000000000 : ℝ))
      (E := (cell13097 ⟨13, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (5226158533997 / 6250000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (88203167039 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_14 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83583967491533 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (275635403653 / 12500000000000 : ℝ))
      (E := (cell13097 ⟨14, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83583967491533 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (275635403653 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_15 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (16709884559113 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102543599079 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨15, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (16709884559113 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102543599079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_16 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83514902422197 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102545602069 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨16, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83514902422197 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102545602069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_17 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83480406337753 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (110254762599 / 5000000000000 : ℝ))
      (E := (cell13097 ⟨17, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83480406337753 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (110254762599 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_18 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83445934508731 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (551274807429 / 25000000000000 : ℝ))
      (E := (cell13097 ⟨18, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83445934508731 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (551274807429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_19 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41705743450901 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (3528165213 / 160000000000 : ℝ))
      (E := (cell13097 ⟨19, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41705743450901 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (3528165213 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13098_0 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (42035076083357 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551228748231 / 25000000000000 : ℝ))
      (E := (cell13098 ⟨0, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (42035076083357 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551228748231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_1 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (42017631662269 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204918965721 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨1, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (42017631662269 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204918965721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_2 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (84000399295329 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (440984599597 / 20000000000000 : ℝ))
      (E := (cell13098 ⟨2, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (84000399295329 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (440984599597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_3 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (16793112008571 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102463491161 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨3, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (16793112008571 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102463491161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_4 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (83930745531073 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (440986208533 / 20000000000000 : ℝ))
      (E := (cell13098 ⟨4, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (83930745531073 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (440986208533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_5 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (83895955724129 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204935013053 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨5, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (83895955724129 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204935013053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_6 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41930595293179 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204939016929 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨6, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41930595293179 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204939016929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_7 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41913225041141 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204943061649 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨7, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41913225041141 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204943061649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_8 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (83791734176607 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102473519123 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨8, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (83791734176607 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102473519123 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_9 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41878521417113 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204951069547 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨9, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41878521417113 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204951069547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_10 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (20930594005053 / 25000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102477552037 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨10, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (20930594005053 / 25000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102477552037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_11 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41843866849911 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551239772501 / 25000000000000 : ℝ))
      (E := (cell13098 ⟨11, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41843866849911 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551239772501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_12 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (83653115838493 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204963091431 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨12, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (83653115838493 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204963091431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_13 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41809261200921 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102483557073 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨13, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41809261200921 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102483557073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_14 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (5223997084729 / 6250000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (440994221103 / 20000000000000 : ℝ))
      (E := (cell13098 ⟨14, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (5223997084729 / 6250000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (440994221103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_15 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (20887352166483 / 25000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (275621891121 / 12500000000000 : ℝ))
      (E := (cell13098 ⟨15, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (20887352166483 / 25000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (275621891121 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_16 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (20878722074699 / 25000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204979131337 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨16, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (20878722074699 / 25000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204979131337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_17 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (83480392220577 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102491587807 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨17, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (83480392220577 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102491587807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_18 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (3337836815911 / 4000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204987149833 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨18, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (3337836815911 / 4000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204987149833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_19 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (4170573639853 / 5000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551247793693 / 25000000000000 : ℝ))
      (E := (cell13098 ⟨19, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (4170573639853 / 5000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551247793693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13099_0 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (84070137945129 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102401460693 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨0, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (84070137945129 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102401460693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_1 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (84035249109267 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102403473859 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨1, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (84035249109267 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102403473859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_2 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (84000385086367 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204810917819 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨2, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (84000385086367 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204810917819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_3 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (16793109168039 / 20000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204814955833 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨3, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (16793109168039 / 20000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204814955833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_4 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83930731334709 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204818954063 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨4, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83930731334709 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204818954063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_5 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (10486992691757 / 12500000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204822978267 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨5, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (10486992691757 / 12500000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204822978267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_6 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (8386117640257 / 10000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102413489033 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨6, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (8386117640257 / 10000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102413489033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_7 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83826435904773 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204830960743 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨7, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83826435904773 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204830960743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_8 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83791720005373 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204834991367 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨8, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83791720005373 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204834991367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_9 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83757028669259 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204839018733 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨9, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83757028669259 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204839018733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_10 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (20930590465377 / 25000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204842991287 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨10, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (20930590465377 / 25000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204842991287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_11 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (669501756379 / 800000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (68901469733 / 3125000000000 : ℝ))
      (E := (cell13099 ⟨11, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (669501756379 / 800000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (68901469733 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_12 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41826550846149 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102425514543 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨12, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41826550846149 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102425514543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_13 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83618508261893 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204855048051 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨13, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83618508261893 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204855048051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_14 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83583939221957 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551214758929 / 25000000000000 : ℝ))
      (E := (cell13099 ⟨14, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83583939221957 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551214758929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_15 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (4177469726923 / 5000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (275607881939 / 12500000000000 : ℝ))
      (E := (cell13099 ⟨15, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (4177469726923 / 5000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (275607881939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_16 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83514874177553 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (34451047723 / 1562500000000 : ℝ))
      (E := (cell13099 ⟨16, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83514874177553 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (34451047723 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_17 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83480378105559 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102435547493 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨17, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83480378105559 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102435547493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_18 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (5215369143061 / 6250000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102437561979 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨18, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (5215369143061 / 6250000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102437561979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_19 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (3336458347779 / 4000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204879145451 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨19, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (3336458347779 / 4000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204879145451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

end BstLean.Part268
