import BstLean.Part268CellShard29Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13075_20 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (16675474839563 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551894631697 / 25000000000000 : ℝ))
      (E := (cell13075 ⟨20, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (16675474839563 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551894631697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_21 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41671487399521 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207582570649 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨21, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41671487399521 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207582570649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_22 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83308599523517 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441517311773 / 20000000000000 : ℝ))
      (E := (cell13075 ⟨22, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83308599523517 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441517311773 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_23 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83274248338591 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207590553063 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨23, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83274248338591 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207590553063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_24 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83239921211783 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207594614729 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨24, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83239921211783 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207594614729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_25 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (10400702263847 / 12500000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (1103799285743 / 50000000000000 : ℝ))
      (E := (cell13075 ⟨25, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (10400702263847 / 12500000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (1103799285743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_26 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83171339003421 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207602601169 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨26, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83171339003421 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207602601169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_27 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20784270964433 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (8830426591 / 400000000000 : ℝ))
      (E := (cell13075 ⟨27, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20784270964433 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (8830426591 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_28 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (2596964145059 / 3125000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (1103805327437 / 50000000000000 : ℝ))
      (E := (cell13075 ⟨28, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (2596964145059 / 3125000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (1103805327437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_29 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (83068645324229 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (275951828049 / 12500000000000 : ℝ))
      (E := (cell13075 ⟨29, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (83068645324229 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (275951828049 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_30 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (16606892374651 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207618675019 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨30, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (16606892374651 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207618675019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_31 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (8300030225763 / 10000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207622691143 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨31, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (8300030225763 / 10000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207622691143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_32 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41483083223087 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (275953334241 / 12500000000000 : ℝ))
      (E := (cell13075 ⟨32, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41483083223087 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (275953334241 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_33 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20733013601967 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207630682929 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨33, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20733013601967 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207630682929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_34 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (10362245763981 / 12500000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207634718931 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨34, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (10362245763981 / 12500000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207634718931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_35 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (82863901527409 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207638723823 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨35, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (82863901527409 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207638723823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_36 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (82829860623999 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (27595534457 / 1250000000000 : ℝ))
      (E := (cell13075 ⟨36, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (82829860623999 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (27595534457 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_37 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (82795843371223 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (110382337927 / 5000000000000 : ℝ))
      (E := (cell13075 ⟨37, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (82795843371223 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (110382337927 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_38 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41380924869419 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207650729583 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨38, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41380924869419 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207650729583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_39 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (16545575939351 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441530957361 / 20000000000000 : ℝ))
      (E := (cell13075 ⟨39, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (16545575939351 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441530957361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13076_20 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (4168868002587 / 5000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207466009167 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨20, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (4168868002587 / 5000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207466009167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_21 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (10417870082399 / 12500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207469991083 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨21, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (10417870082399 / 12500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207469991083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_22 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83308585389887 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (88298961363 / 4000000000000 : ℝ))
      (E := (cell13076 ⟨22, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83308585389887 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (88298961363 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_23 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (3330969368447 / 4000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103739012379 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨23, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (3330969368447 / 4000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103739012379 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_24 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (3329596283623 / 4000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (44149640491 / 2000000000000 : ℝ))
      (E := (cell13076 ⟨24, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (3329596283623 / 4000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (44149640491 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_25 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (20801400998943 / 25000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207486036293 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨25, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (20801400998943 / 25000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207486036293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_26 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (16634264978923 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207490062601 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨26, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (16634264978923 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207490062601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_27 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (1039213371939 / 1250000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103747023687 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨27, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (1039213371939 / 1250000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103747023687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_28 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83102838545463 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103749025597 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨28, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83102838545463 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103749025597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_29 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41534315616993 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103751037989 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨29, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41534315616993 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103751037989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_30 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (8303444778919 / 10000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (441501224683 / 20000000000000 : ℝ))
      (E := (cell13076 ⟨30, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (8303444778919 / 10000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (441501224683 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_31 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (83000288179737 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551877534099 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨31, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (83000288179737 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551877534099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_32 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (5185384523403 / 6250000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551878529021 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨32, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (5185384523403 / 6250000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551878529021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_33 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82932040342303 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551879530509 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨33, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82932040342303 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551879530509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_34 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (2072448801311 / 2500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207522155033 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨34, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (2072448801311 / 2500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207522155033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_35 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (10357985934269 / 12500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (275940769621 / 12500000000000 : ℝ))
      (E := (cell13076 ⟨35, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (10357985934269 / 12500000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (275940769621 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_36 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82829846576889 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207530186793 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨36, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82829846576889 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207530186793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_37 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41397914665127 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551883546477 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨37, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41397914665127 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551883546477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_38 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (16552367140801 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551884553217 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨38, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (16552367140801 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551884553217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_39 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82727865668053 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207542208581 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨39, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82727865668053 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207542208581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13077_20 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (10422168238479 / 12500000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207353428947 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨20, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (10422168238479 / 12500000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207353428947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_21 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (20835736630377 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (220735746557 / 10000000000000 : ℝ))
      (E := (cell13077 ⟨21, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (20835736630377 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (220735746557 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_22 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83308571258421 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207361446641 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨22, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83308571258421 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207361446641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_23 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41637110042961 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207365492173 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨23, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41637110042961 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207365492173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_24 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (8323989297153 / 10000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207369488497 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨24, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (8323989297153 / 10000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207369488497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_25 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83205589882929 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207373496821 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨25, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83205589882929 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207373496821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_26 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (8317131078797 / 10000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103688759877 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨26, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (8317131078797 / 10000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103688759877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_27 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41568527827333 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (5518453753 / 250000000000 : ℝ))
      (E := (cell13077 ⟨27, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41568527827333 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (5518453753 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_28 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83102824451197 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207385560239 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨28, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83102824451197 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207385560239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_29 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83068617145901 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551847395453 / 25000000000000 : ℝ))
      (E := (cell13077 ⟨29, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83068617145901 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551847395453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_30 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83034433707281 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207393567537 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨30, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83034433707281 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207393567537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_31 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (83000274103999 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (68981174293 / 3125000000000 : ℝ))
      (E := (cell13077 ⟨31, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (83000274103999 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (68981174293 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_32 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (20741534576219 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207401612563 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨32, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (20741534576219 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207401612563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_33 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (82932026278893 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (17245356371 / 781250000000 : ℝ))
      (E := (cell13077 ⟨33, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (82932026278893 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (17245356371 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_34 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (16579587599037 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (137963099179 / 6250000000000 : ℝ))
      (E := (cell13077 ⟨34, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (16579587599037 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (137963099179 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_35 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (10357984177881 / 12500000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207413644507 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨35, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (10357984177881 / 12500000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207413644507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_36 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (8282983253193 / 10000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551854403189 / 25000000000000 : ℝ))
      (E := (cell13077 ⟨36, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (8282983253193 / 10000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551854403189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_37 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (16559163058287 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (55185541693 / 2500000000000 : ℝ))
      (E := (cell13077 ⟨37, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (16559163058287 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (55185541693 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_38 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41380910835661 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551856422971 / 25000000000000 : ℝ))
      (E := (cell13077 ⟨38, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41380910835661 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551856422971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_39 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (165455703283 / 200000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (137964355303 / 6250000000000 : ℝ))
      (E := (cell13077 ⟨39, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (165455703283 / 200000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (137964355303 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13078_20 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83377331766089 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103620480537 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨20, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83377331766089 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103620480537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_21 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (20835733096497 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207244935777 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨21, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (20835733096497 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207244935777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_22 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83308557129119 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (44144979433 / 2000000000000 : ℝ))
      (E := (cell13078 ⟨22, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83308557129119 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (44144979433 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_23 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (5204637872677 / 6250000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207252955309 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨23, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (5204637872677 / 6250000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207252955309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_24 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83239878854647 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (88290280263 / 4000000000000 : ℝ))
      (E := (cell13078 ⟨24, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83239878854647 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (88290280263 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_25 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (10400696971531 / 12500000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207261011501 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨25, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (10400696971531 / 12500000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207261011501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_26 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (16634259336697 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (441453006217 / 20000000000000 : ℝ))
      (E := (cell13078 ⟨26, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (16634259336697 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (441453006217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_27 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (20784260389093 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (551817252307 / 25000000000000 : ℝ))
      (E := (cell13078 ⟨27, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (20784260389093 / 25000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (551817252307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_28 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (5193925647443 / 6250000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (220727300651 / 10000000000000 : ℝ))
      (E := (cell13078 ⟨28, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (5193925647443 / 6250000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (220727300651 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_29 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83068603059973 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (137954814053 / 6250000000000 : ℝ))
      (E := (cell13078 ⟨29, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83068603059973 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (137954814053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_30 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83034419627529 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207281065933 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨30, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83034419627529 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207281065933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_31 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (83000260030417 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103642536327 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨31, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (83000260030417 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103642536327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_32 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82966124237459 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207289104771 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨32, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82966124237459 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207289104771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_33 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (16586402443527 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207293104671 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨33, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (16586402443527 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207293104671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_34 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82897923940083 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207297073067 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨34, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82897923940083 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207297073067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_35 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (16572771874819 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103650563889 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨35, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (16572771874819 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103650563889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_36 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82829818489121 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (220730515183 / 10000000000000 : ℝ))
      (E := (cell13078 ⟨36, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82829818489121 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (220730515183 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_37 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (41397900627383 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (137956821579 / 6250000000000 : ℝ))
      (E := (cell13078 ⟨37, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (41397900627383 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (137956821579 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_38 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82761807640787 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103656583317 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨38, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82761807640787 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103656583317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_39 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (16545567523419 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207317156851 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨39, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (16545567523419 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207317156851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13079_20 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (5211082351657 / 6250000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103564215303 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨20, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (5211082351657 / 6250000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103564215303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_21 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (10417864781579 / 12500000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207132460043 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨21, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (10417864781579 / 12500000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207132460043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_22 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (4165427150099 / 5000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207136492381 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨22, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (4165427150099 / 5000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207136492381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_23 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16654838368381 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (44142809451 / 2000000000000 : ℝ))
      (E := (cell13079 ⟨23, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16654838368381 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (44142809451 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_24 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (3329594589597 / 4000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207144461967 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨24, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (3329594589597 / 4000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207144461967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_25 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83205561663727 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103574260953 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨25, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83205561663727 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103574260953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_26 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83171282581159 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103576269071 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨26, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83171282581159 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103576269071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_27 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (83137027460237 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207156512981 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨27, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (83137027460237 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207156512981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_28 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41551398134569 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551790141377 / 25000000000000 : ℝ))
      (E := (cell13079 ⟨28, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41551398134569 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551790141377 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_29 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41534294488101 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (275895565267 / 12500000000000 : ℝ))
      (E := (cell13079 ⟨29, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41534294488101 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (275895565267 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_30 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (20758601387483 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103584280029 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨30, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (20758601387483 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103584280029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_31 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (8300024595899 / 10000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103586281831 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨31, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (8300024595899 / 10000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103586281831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_32 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (20741527543049 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551794148177 / 25000000000000 : ℝ))
      (E := (cell13079 ⟨32, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (20741527543049 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551794148177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_33 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82931998158531 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (137948786849 / 6250000000000 : ℝ))
      (E := (cell13079 ⟨33, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82931998158531 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (137948786849 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_34 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (20724477471783 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551796153411 / 25000000000000 : ℝ))
      (E := (cell13079 ⟨34, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (20724477471783 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551796153411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_35 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82863845327293 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207188606781 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨35, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82863845327293 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207188606781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_36 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82829804448463 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207192627947 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨36, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82829804448463 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207192627947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_37 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41397893610123 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441439335451 / 20000000000000 : ℝ))
      (E := (cell13079 ⟨37, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41397893610123 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441439335451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_38 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82761793612401 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207200637119 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨38, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82761793612401 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207200637119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_39 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (20681955898709 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207204683349 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨39, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (20681955898709 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207204683349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13080_20 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83377303489099 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551753988543 / 25000000000000 : ℝ))
      (E := (cell13080 ⟨20, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83377303489099 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551753988543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_21 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83342904121441 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551754995007 / 25000000000000 : ℝ))
      (E := (cell13080 ⟨21, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83342904121441 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551754995007 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_22 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (20827132219251 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (17242375069 / 781250000000 : ℝ))
      (E := (cell13080 ⟨22, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (20827132219251 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (17242375069 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_23 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83274177723139 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103513992757 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨23, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83274177723139 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103513992757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_24 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (16647970125473 / 20000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207032029897 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨24, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (16647970125473 / 20000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207032029897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_25 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41602773778683 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (441407205607 / 20000000000000 : ℝ))
      (E := (cell13080 ⟨25, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41602773778683 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (441407205607 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_26 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (2599102140031 / 3125000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207040040923 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨26, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (2599102140031 / 3125000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207040040923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_27 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83137013366259 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207044070939 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨27, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83137013366259 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207044070939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_28 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (2596961943167 / 3125000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207048061733 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨28, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (2596961943167 / 3125000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207048061733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_29 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (20767143723647 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551763018419 / 25000000000000 : ℝ))
      (E := (cell13080 ⟨29, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (20767143723647 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551763018419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_30 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83034391474491 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207056108459 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨30, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83034391474491 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207056108459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_31 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (83000231889717 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (220706010897 / 10000000000000 : ℝ))
      (E := (cell13080 ⟨31, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (83000231889717 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (220706010897 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_32 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41483048054543 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (220706413497 / 10000000000000 : ℝ))
      (E := (cell13080 ⟨32, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41483048054543 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (220706413497 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_33 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82931984101579 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103534064423 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨33, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82931984101579 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103534064423 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_34 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82897895836333 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207072149953 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨34, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82897895836333 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207072149953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_35 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82863831282641 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207076140183 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨35, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82863831282641 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207076140183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_36 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41414895204977 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (275885019811 / 12500000000000 : ℝ))
      (E := (cell13080 ⟨36, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41414895204977 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (275885019811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_37 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (662366185503 / 800000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (110354210249 / 5000000000000 : ℝ))
      (E := (cell13080 ⟨37, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (662366185503 / 800000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (110354210249 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_38 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41380889793081 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551772055203 / 25000000000000 : ℝ))
      (E := (cell13080 ⟨38, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41380889793081 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551772055203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_39 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (3309112382989 / 4000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207092205583 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨39, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (3309112382989 / 4000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207092205583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13081_20 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (83377289353851 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206903531773 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨20, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (83377289353851 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206903531773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_21 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (20835722498103 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103453777037 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨21, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (20835722498103 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103453777037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_22 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (8330851475419 / 10000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206911521007 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨22, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (8330851475419 / 10000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206911521007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_23 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (16654832721307 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103457776293 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨23, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (16654832721307 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103457776293 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_24 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (20809959129241 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103459796777 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨24, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (20809959129241 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103459796777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_25 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (20801383363291 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206923588321 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨25, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (20801383363291 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206923588321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_26 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (10396406797873 / 12500000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441385519577 / 20000000000000 : ℝ))
      (E := (cell13081 ⟨26, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (10396406797873 / 12500000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441385519577 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_27 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (83136999274439 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (17655452997 / 800000000000 : ℝ))
      (E := (cell13081 ⟨27, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (83136999274439 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (17655452997 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_28 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (83102768095707 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206935612187 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨28, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (83102768095707 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206935612187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_29 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (83068560815129 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441387924189 / 20000000000000 : ℝ))
      (E := (cell13081 ⟨29, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (83068560815129 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441387924189 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_30 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (16606875480241 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220694365259 / 10000000000000 : ℝ))
      (E := (cell13081 ⟨30, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (16606875480241 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220694365259 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_31 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41500108911299 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220694765001 / 10000000000000 : ℝ))
      (E := (cell13081 ⟨31, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41500108911299 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220694765001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_32 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (82966082048129 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441390334593 / 20000000000000 : ℝ))
      (E := (cell13081 ⟨32, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (82966082048129 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441390334593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_33 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (82931970046779 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206955663841 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨33, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (82931970046779 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206955663841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_34 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (16579576357537 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441391936399 / 20000000000000 : ℝ))
      (E := (cell13081 ⟨34, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (16579576357537 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441391936399 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_35 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (4143190862007 / 5000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (137935232999 / 6250000000000 : ℝ))
      (E := (cell13081 ⟨35, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (4143190862007 / 5000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (137935232999 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_36 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41414888186797 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206967743453 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨36, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41414888186797 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206967743453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_37 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (20698939789413 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206971728441 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨37, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (20698939789413 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206971728441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_38 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (8276176556207 / 10000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103487870753 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨38, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (8276176556207 / 10000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103487870753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_39 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (2068194888919 / 2500000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103489891157 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨39, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (2068194888919 / 2500000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103489891157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13082_20 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (41688637610383 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (275848888137 / 12500000000000 : ℝ))
      (E := (cell13082 ⟨20, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (41688637610383 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (275848888137 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_21 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83342875865547 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (3448117381 / 156250000000 : ℝ))
      (E := (cell13082 ⟨21, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83342875865547 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (3448117381 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_22 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (41654250316769 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206799145627 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨22, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (41654250316769 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206799145627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_23 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83274149492091 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206803115383 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨23, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83274149492091 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206803115383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_24 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20809955602181 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103403576467 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨24, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20809955602181 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103403576467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_25 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (41602759675561 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551702786083 / 25000000000000 : ℝ))
      (E := (cell13082 ⟨25, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (41602759675561 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551702786083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_26 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (41585620143567 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206815150573 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨26, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (41585620143567 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206815150573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_27 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83136985184777 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551704793509 / 25000000000000 : ℝ))
      (E := (cell13082 ⟨27, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83136985184777 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551704793509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_28 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (83102754012227 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (220682321687 / 10000000000000 : ℝ))
      (E := (cell13082 ⟨28, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (83102754012227 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (220682321687 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_29 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (3322741869513 / 4000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206827222469 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨29, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (3322741869513 / 4000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206827222469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_30 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (10379295416259 / 12500000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551707798113 / 25000000000000 : ℝ))
      (E := (cell13082 ⟨30, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (10379295416259 / 12500000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551707798113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_31 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (1296878183713 / 1562500000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206835245353 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨31, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (1296878183713 / 1562500000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206835245353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_32 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (3318642719573 / 4000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (441367853057 / 20000000000000 : ℝ))
      (E := (cell13082 ⟨32, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (3318642719573 / 4000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (441367853057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_33 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82931955994131 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206843253187 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨33, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82931955994131 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206843253187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_34 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82897867741187 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103423634207 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨34, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82897867741187 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103423634207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_35 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20715950799947 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103425626427 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨35, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20715950799947 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103425626427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_36 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82829762339383 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206855265463 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨36, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82829762339383 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206855265463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_37 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (10349468141197 / 12500000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (137928706647 / 6250000000000 : ℝ))
      (E := (cell13082 ⟨37, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (10349468141197 / 12500000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (137928706647 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_38 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (662094012321 / 800000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (34482239323 / 1562500000000 : ℝ))
      (E := (cell13082 ⟨38, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (662094012321 / 800000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (34482239323 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_39 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (4136389077047 / 5000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (68964604837 / 3125000000000 : ℝ))
      (E := (cell13082 ⟨39, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (4136389077047 / 5000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (68964604837 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13083_20 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (20844315272461 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206678674143 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨20, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (20844315272461 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206678674143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_21 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83342861740843 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206682689333 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨21, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83342861740843 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206682689333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_22 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (10413560814381 / 12500000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206686707611 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨22, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (10413560814381 / 12500000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206686707611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_23 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (2602316730619 / 3125000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206690732291 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨23, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (2602316730619 / 3125000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206690732291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_24 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83239808302643 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206694766451 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨24, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83239808302643 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206694766451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_25 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41602752625619 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206698754503 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨25, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41602752625619 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206698754503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_26 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41585613096721 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103351378723 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨26, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41585613096721 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103351378723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_27 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83136971097271 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (275838347207 / 12500000000000 : ℝ))
      (E := (cell13083 ⟨27, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83136971097271 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (275838347207 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_28 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41551369965451 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206710758783 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨28, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41551369965451 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206710758783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_29 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (3322741306507 / 4000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103357409863 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨29, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (3322741306507 / 4000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103357409863 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_30 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41517174630547 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103359393297 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨30, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41517174630547 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103359393297 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_31 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (83000189694819 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206722836429 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨31, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (83000189694819 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206722836429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_32 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (648172296349 / 781250000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103363426671 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨32, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (648172296349 / 781250000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103363426671 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_33 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (82931941943633 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (220673083827 / 10000000000000 : ℝ))
      (E := (cell13083 ⟨33, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (82931941943633 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (220673083827 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_34 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (2072446342421 / 2500000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (275841856321 / 12500000000000 : ℝ))
      (E := (cell13083 ⟨34, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (2072446342421 / 2500000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (275841856321 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_35 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41431894580793 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206738890793 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨35, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41431894580793 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206738890793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_36 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (2070743707683 / 2500000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206742900591 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨36, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (2070743707683 / 2500000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206742900591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_37 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (2587366596989 / 3125000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206746880001 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨37, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (2587366596989 / 3125000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206746880001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_38 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41380868760163 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206750887579 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨38, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41380868760163 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206750887579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_39 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41363883763633 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103377461497 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨39, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41363883763633 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103377461497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13084_20 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41688623480543 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206566297227 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨20, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41688623480543 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206566297227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_21 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41671423809151 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206570308887 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨21, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41671423809151 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206570308887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_22 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41654236199359 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103287161841 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨22, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41654236199359 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103287161841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_23 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (16654824253937 / 20000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551644586231 / 25000000000000 : ℝ))
      (E := (cell13084 ⟨23, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (16654824253937 / 20000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551644586231 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_24 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83239794198721 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103291187847 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨24, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83239794198721 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103291187847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_25 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (10400686394189 / 12500000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103293180201 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨25, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (10400686394189 / 12500000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103293180201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_26 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83171212101907 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103295180023 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨26, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83171212101907 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103295180023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_27 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (83136957011921 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103297188503 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨27, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (83136957011921 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103297188503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_28 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (20775681462933 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206598413431 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨28, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (20775681462933 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206598413431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_29 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (1038356482371 / 1250000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206602412713 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨29, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (1038356482371 / 1250000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206602412713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_30 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (20758583798567 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206606435019 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨30, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (20758583798567 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206606435019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_31 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41500087817079 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103305211619 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨31, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41500087817079 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103305211619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_32 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (8296603987817 / 10000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551653609283 / 25000000000000 : ℝ))
      (E := (cell13084 ⟨32, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (8296603987817 / 10000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551653609283 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_33 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41465963947643 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103309238853 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨33, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41465963947643 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103309238853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_34 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82897839654641 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206622487101 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨34, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82897839654641 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206622487101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_35 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82863775125531 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206626465803 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨35, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82863775125531 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206626465803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_36 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (16565946855481 / 20000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441326106291 / 20000000000000 : ℝ))
      (E := (cell13084 ⟨36, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (16565946855481 / 20000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441326106291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_37 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41397858539933 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206634508101 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨37, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41397858539933 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206634508101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_38 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82761723502673 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206638512961 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨38, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82761723502673 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206638512961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_39 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82727753515737 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206642545703 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨39, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82727753515737 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206642545703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13085_20 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83377232834489 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206453974353 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨20, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83377232834489 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206453974353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_21 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (41671416748961 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103228991253 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨21, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (41671416748961 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103228991253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_22 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83308458284549 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206461993841 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨22, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83308458284549 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206461993841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_23 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83274107161721 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103232976643 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨23, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83274107161721 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103232976643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_24 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (41619890048479 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103234990333 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨24, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (41619890048479 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103234990333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_25 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83205477057943 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206474020463 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨25, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83205477057943 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206474020463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_26 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (5198199875783 / 6250000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103239008417 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨26, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (5198199875783 / 6250000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103239008417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_27 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (41568471464363 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (275810253821 / 12500000000000 : ℝ))
      (E := (cell13085 ⟨27, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (41568471464363 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (275810253821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_28 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (20775677943679 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (551621515953 / 25000000000000 : ℝ))
      (E := (cell13085 ⟨28, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (20775677943679 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (551621515953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_29 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83068504518839 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103245029979 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨29, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83068504518839 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103245029979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_30 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (20758580282399 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206494079177 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨30, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (20758580282399 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206494079177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_31 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (83000161575649 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (441299612871 / 20000000000000 : ℝ))
      (E := (cell13085 ⟨31, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (83000161575649 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (441299612871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_32 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (4148301291291 / 5000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206502075253 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨32, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (4148301291291 / 5000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206502075253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_33 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82931913849089 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103253056439 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨33, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82931913849089 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103253056439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_34 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (323819631307 / 390625000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206510119371 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨34, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (323819631307 / 390625000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206510119371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_35 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (662910088733 / 800000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206514153883 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨35, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (662910088733 / 800000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206514153883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_36 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82829720249637 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206518158059 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨36, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82829720249637 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206518158059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_37 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82795703058231 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206522131941 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨37, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82795703058231 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206522131941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_38 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (41380854743583 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (110326309641 / 5000000000000 : ℝ))
      (E := (cell13085 ⟨38, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (41380854743583 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (110326309641 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_39 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (5170483719147 / 6250000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103265082077 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨39, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (5170483719147 / 6250000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103265082077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13086_20 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41688609355027 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206341588889 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨20, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41688609355027 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206341588889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_21 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41671409689851 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103172796757 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨21, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41671409689851 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103172796757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_22 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83308444172539 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (275793700171 / 12500000000000 : ℝ))
      (E := (cell13086 ⟨22, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83308444172539 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (275793700171 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_23 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20818523263979 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103176807881 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨23, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20818523263979 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103176807881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_24 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (10404970749669 / 12500000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (68948676243 / 3125000000000 : ℝ))
      (E := (cell13086 ⟨24, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (10404970749669 / 12500000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (68948676243 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_25 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20801365741133 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103180838127 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨25, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20801365741133 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103180838127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_26 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (16634236785061 / 20000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206365669353 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨26, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (16634236785061 / 20000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206365669353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_27 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83136928847687 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (110318483993 / 5000000000000 : ℝ))
      (E := (cell13086 ⟨27, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83136928847687 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (110318483993 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_28 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (16620539539971 / 20000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (88254948397 / 4000000000000 : ℝ))
      (E := (cell13086 ⟨28, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (16620539539971 / 20000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (88254948397 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_29 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83068490450151 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103188851469 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨29, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83068490450151 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103188851469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_30 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20758576766769 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206381719069 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨30, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20758576766769 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206381719069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_31 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (83000147519291 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206385759781 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨31, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (83000147519291 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206385759781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_32 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (4148300588781 / 5000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206389767707 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨32, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (4148300588781 / 5000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206389767707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_33 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82931899805041 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206393743789 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨33, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82931899805041 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206393743789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_34 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20724452894173 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103198903011 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨34, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20724452894173 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103198903011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_35 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82863747059867 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551600444759 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨35, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82863747059867 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551600444759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_36 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (16565941244803 / 20000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551601445101 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨36, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (16565941244803 / 20000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551601445101 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_37 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82795689038741 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551602452559 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨37, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82795689038741 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551602452559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_38 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82761695473803 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551603452421 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨38, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82761695473803 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551603452421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_39 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82727725499111 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551604459277 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨39, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82727725499111 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551604459277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13087_20 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83377204587781 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206229315783 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨20, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83377204587781 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206229315783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_21 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83342805263643 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (34472395577 / 1562500000000 : ℝ))
      (E := (cell13087 ⟨21, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83342805263643 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (34472395577 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_22 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83308430062689 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206237321347 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨22, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83308430062689 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206237321347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_23 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (8327407895227 / 10000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206241332353 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨23, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (8327407895227 / 10000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206241332353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_24 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (325155280859 / 390625000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206245353027 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨24, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (325155280859 / 390625000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206245353027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_25 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (20801362218319 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206249327779 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨25, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (20801362218319 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206249327779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_26 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41585584920119 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (110312668803 / 5000000000000 : ℝ))
      (E := (cell13087 ⟨26, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41585584920119 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (110312668803 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_27 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41568457384401 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103128691683 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨27, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41568457384401 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103128691683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_28 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (20775670906787 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (88250456411 / 4000000000000 : ℝ))
      (E := (cell13087 ⟨28, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (20775670906787 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (88250456411 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_29 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (648972471747 / 781250000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206265400179 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨29, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (648972471747 / 781250000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206265400179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_30 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (83034293006707 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206269413249 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨30, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (83034293006707 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206269413249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_31 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (16600026693017 / 20000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (220627339237 / 10000000000000 : ℝ))
      (E := (cell13087 ⟨31, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (16600026693017 / 20000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (220627339237 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_32 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (8296599772757 / 10000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (22062774559 / 1000000000000 : ℝ))
      (E := (cell13087 ⟨32, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (8296599772757 / 10000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (22062774559 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_33 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41465942881571 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103140714529 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨33, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41465942881571 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103140714529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_34 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82897797540939 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103142744207 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨34, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82897797540939 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103142744207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_35 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (16572746606051 / 20000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206289458597 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨35, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (16572746606051 / 20000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206289458597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_36 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (4141484610027 / 5000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206293515869 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨36, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (4141484610027 / 5000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206293515869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_37 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82795675021397 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (137893592767 / 6250000000000 : ℝ))
      (E := (cell13087 ⟨37, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82795675021397 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (137893592767 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_38 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (10345210182823 / 12500000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103150769883 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨38, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (10345210182823 / 12500000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103150769883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_39 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82727711494013 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206305505807 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨39, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82727711494013 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206305505807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13088_20 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (20844297616917 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (220611698009 / 10000000000000 : ℝ))
      (E := (cell13088 ⟨20, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (20844297616917 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (220611698009 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_21 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (5208924446859 / 6250000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (220612097773 / 10000000000000 : ℝ))
      (E := (cell13088 ⟨21, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (5208924446859 / 6250000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (220612097773 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_22 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41654207977499 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441225007411 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨22, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41654207977499 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441225007411 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_23 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83274064850781 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (88245161787 / 4000000000000 : ℝ))
      (E := (cell13088 ⟨23, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83274064850781 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (88245161787 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_24 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83239737804613 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (275766632751 / 12500000000000 : ℝ))
      (E := (cell13088 ⟨24, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83239737804613 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (275766632751 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_25 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83205434784177 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103068516733 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨25, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83205434784177 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103068516733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_26 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (3326846230293 / 4000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206141078501 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨26, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (3326846230293 / 4000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206141078501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_27 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (10392112586509 / 12500000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441229016521 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨27, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (10392112586509 / 12500000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441229016521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_28 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41551334778297 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206149106359 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨28, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41551334778297 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206149106359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_29 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (83068462319233 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (551538273289 / 25000000000000 : ℝ))
      (E := (cell13088 ⟨29, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (83068462319233 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (551538273289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_30 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (8303427894849 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206157103163 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨30, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (8303427894849 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206157103163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_31 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (20750029853257 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103080568921 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨31, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (20750029853257 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103080568921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_32 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82965983681669 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (220616513983 / 10000000000000 : ℝ))
      (E := (cell13088 ⟨32, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82965983681669 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (220616513983 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_33 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (647905247839 / 781250000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441233833737 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨33, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (647905247839 / 781250000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441233833737 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_34 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41448891753667 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441234633309 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨34, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41448891753667 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441234633309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_35 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (8286371900279 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441235438513 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨35, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (8286371900279 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441235438513 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_36 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (8282967817921 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103090594193 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨36, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (8282967817921 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103090594193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_37 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82795661006197 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441237042553 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨37, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82795661006197 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441237042553 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_38 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82761667453509 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103094603427 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨38, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82761667453509 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103094603427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_39 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41363848745529 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (220619322901 / 10000000000000 : ℝ))
      (E := (cell13088 ⟨39, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41363848745529 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (220619322901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13089_20 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20844294087429 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (55150117461 / 2500000000000 : ℝ))
      (E := (cell13089 ⟨20, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20844294087429 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (55150117461 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_21 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20835694259501 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206008750941 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨21, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20835694259501 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206008750941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_22 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (16661680369893 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441202549699 / 20000000000000 : ℝ))
      (E := (cell13089 ⟨22, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (16661680369893 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441202549699 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_23 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (1665481015029 / 2000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206016752729 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨23, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (1665481015029 / 2000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206016752729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_24 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41619861855739 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206020766723 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨24, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41619861855739 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206020766723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_25 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41602710348617 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (55150619833 / 2500000000000 : ℝ))
      (E := (cell13089 ⟨25, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41602710348617 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (55150619833 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_26 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (10396392709571 / 12500000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (551507194169 / 25000000000000 : ℝ))
      (E := (cell13089 ⟨26, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (10396392709571 / 12500000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (551507194169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_27 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (16627377323499 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (110301638879 / 5000000000000 : ℝ))
      (E := (cell13089 ⟨27, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (16627377323499 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (110301638879 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_28 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (1298478992003 / 1562500000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206036798181 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨28, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (1298478992003 / 1562500000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206036798181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_29 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (83068448257001 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206040840397 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨29, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (83068448257001 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206040840397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_30 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (10379283111553 / 12500000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103022423683 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨30, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (10379283111553 / 12500000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103022423683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_31 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41500052681561 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206048820481 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨31, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41500052681561 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206048820481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_32 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82965969637917 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206052878097 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨32, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82965969637917 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206052878097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_33 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82931857685789 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103028422717 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨33, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82931857685789 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103028422717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_34 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20724442368969 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103030449531 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨34, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20724442368969 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103030449531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_35 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82863704977471 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (88242596891 / 4000000000000 : ℝ))
      (E := (cell13089 ⟨35, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82863704977471 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (88242596891 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_36 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (3313186566401 / 4000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206068915337 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨36, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (3313186566401 / 4000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206068915337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_37 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82795646993141 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206072937003 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨37, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82795646993141 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206072937003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_38 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41380826723289 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (275759616053 / 12500000000000 : ℝ))
      (E := (cell13089 ⟨38, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41380826723289 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (275759616053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_39 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (16545536698049 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206080947959 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨39, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (16545536698049 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206080947959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13090_20 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83377162233923 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205892470837 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨20, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83377162233923 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205892470837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_21 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83342762928423 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (275737057693 / 12500000000000 : ℝ))
      (E := (cell13090 ⟨21, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83342762928423 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (275737057693 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_22 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (8330838774609 / 10000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102950227833 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨22, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (8330838774609 / 10000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102950227833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_23 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (20818509163569 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205904514901 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨23, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (20818509163569 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205904514901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_24 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (166479419241 / 200000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205908525579 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨24, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (166479419241 / 200000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205908525579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_25 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41602703306223 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102956245237 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨25, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41602703306223 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102956245237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_26 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (20792781899491 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102958264521 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨26, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (20792781899491 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102958264521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_27 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83136872545071 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (220592052677 / 10000000000000 : ℝ))
      (E := (cell13090 ⟨27, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83136872545071 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (220592052677 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_28 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83102641421943 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205924544241 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨28, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83102641421943 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205924544241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_29 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (83068434196921 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102964291687 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨29, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (83068434196921 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102964291687 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_30 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (20758562709627 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205932587307 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨30, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (20758562709627 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205932587307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_31 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (16600018263073 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551484154001 / 25000000000000 : ℝ))
      (E := (cell13090 ⟨31, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (16600018263073 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551484154001 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_32 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82965955596313 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441188122421 / 20000000000000 : ℝ))
      (E := (cell13090 ⟨32, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82965955596313 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441188122421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_33 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41465921825167 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205944635163 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨33, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41465921825167 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205944635163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_34 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (20724438861641 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (55148715683 / 2500000000000 : ℝ))
      (E := (cell13090 ⟨34, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (20724438861641 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (55148715683 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_35 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41431845477149 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (137872040483 / 6250000000000 : ℝ))
      (E := (cell13090 ⟨35, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41431845477149 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (137872040483 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_36 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (16565930028597 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (137872289877 / 6250000000000 : ℝ))
      (E := (cell13090 ⟨36, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (16565930028597 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (137872289877 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_37 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82795632982229 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441192131397 / 20000000000000 : ℝ))
      (E := (cell13090 ⟨37, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82795632982229 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441192131397 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_38 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82761639441789 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551491176119 / 25000000000000 : ℝ))
      (E := (cell13090 ⟨38, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82761639441789 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551491176119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_39 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41363834745787 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441193744283 / 20000000000000 : ℝ))
      (E := (cell13090 ⟨39, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41363834745787 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441193744283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13091_20 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (8337714812029 / 10000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441156047793 / 20000000000000 : ℝ))
      (E := (cell13091 ⟨20, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (8337714812029 / 10000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441156047793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_21 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (83342748821 / 100000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102892113109 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨21, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (83342748821 / 100000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102892113109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_22 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (10413546705609 / 12500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (68930883603 / 3125000000000 : ℝ))
      (E := (cell13091 ⟨22, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (10413546705609 / 12500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (68930883603 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_23 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41637011279629 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205792272807 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨23, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41637011279629 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205792272807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_24 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20809923882919 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205796280171 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨24, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20809923882919 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205796280171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_25 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20801348132453 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205800300231 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨25, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20801348132453 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205800300231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_26 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41585556760757 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441160855429 / 20000000000000 : ℝ))
      (E := (cell13091 ⟨26, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41585556760757 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441160855429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_27 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (207842146187 / 250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205808330177 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨27, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (207842146187 / 250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205808330177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_28 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (16620525471569 / 20000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (68931635767 / 3125000000000 : ℝ))
      (E := (cell13091 ⟨28, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (16620525471569 / 20000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (68931635767 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_29 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (5191776258687 / 6250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205816322091 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨29, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (5191776258687 / 6250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205816322091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_30 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41517118393371 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551455080747 / 25000000000000 : ℝ))
      (E := (cell13091 ⟨30, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41517118393371 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551455080747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_31 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20750019317439 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205824348697 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨31, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20750019317439 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205824348697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_32 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41482970778429 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (44116568009 / 2000000000000 : ℝ))
      (E := (cell13091 ⟨32, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41482970778429 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (44116568009 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_33 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41465914808513 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (68932261313 / 3125000000000 : ℝ))
      (E := (cell13091 ⟨33, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41465914808513 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (68932261313 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_34 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82897741419399 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441167281993 / 20000000000000 : ℝ))
      (E := (cell13091 ⟨34, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82897741419399 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441167281993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_35 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (8286367693327 / 10000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205840427593 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨35, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (8286367693327 / 10000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205840427593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_36 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82829636128089 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102922207581 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨36, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82829636128089 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102922207581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_37 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82795618973461 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102924215713 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨37, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82795618973461 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102924215713 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_38 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41380812719571 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205852476277 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨38, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41380812719571 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205852476277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_39 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (16545531099009 / 20000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205856490619 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨39, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (16545531099009 / 20000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205856490619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13092_20 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (16675426801763 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (88226720113 / 4000000000000 : ℝ))
      (E := (cell13092 ⟨20, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (16675426801763 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (88226720113 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_21 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (16668546943147 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551418011241 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨21, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (16668546943147 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551418011241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_22 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (20827089886453 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441135206459 / 20000000000000 : ℝ))
      (E := (cell13092 ⟨22, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (20827089886453 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441135206459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_23 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (20818502116599 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (137855001653 / 6250000000000 : ℝ))
      (E := (cell13092 ⟨23, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (20818502116599 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (137855001653 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_24 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (5202480090313 / 6250000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205684088907 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨24, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (5202480090313 / 6250000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205684088907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_25 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (20801344612333 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205688047291 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨25, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (20801344612333 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205688047291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_26 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41585549723609 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (27571150993 / 1250000000000 : ℝ))
      (E := (cell13092 ⟨26, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41585549723609 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (27571150993 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_27 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83136844406681 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205696070843 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨27, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83136844406681 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205696070843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_28 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83102613295899 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441140028117 / 20000000000000 : ℝ))
      (E := (cell13092 ⟨28, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83102613295899 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441140028117 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_29 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (83068406083213 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102852057537 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨29, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (83068406083213 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102852057537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_30 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (664273781897 / 800000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (6892837853 / 312500000000 : ℝ))
      (E := (cell13092 ⟨30, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (664273781897 / 800000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (6892837853 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_31 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (10375007903287 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (275714016963 / 12500000000000 : ℝ))
      (E := (cell13092 ⟨31, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (10375007903287 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (275714016963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_32 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (1659318550391 / 2000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102858092269 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨32, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (1659318550391 / 2000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102858092269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_33 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (16586363117173 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205720201851 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨33, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (16586363117173 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205720201851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_34 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82897727394379 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441144837671 / 20000000000000 : ℝ))
      (E := (cell13092 ⟨34, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82897727394379 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441144837671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_35 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82863662914387 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102864101601 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨35, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82863662914387 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102864101601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_36 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82829622115337 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102866094019 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨36, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82829622115337 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102866094019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_37 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (16559120993367 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441147240323 / 20000000000000 : ℝ))
      (E := (cell13092 ⟨37, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (16559120993367 / 20000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441147240323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_38 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41380805719319 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (137858765239 / 6250000000000 : ℝ))
      (E := (cell13092 ⟨38, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41380805719319 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (137858765239 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_39 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (5170477593791 / 6250000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551436063893 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨39, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (5170477593791 / 6250000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551436063893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13093_20 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83377119899499 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102777910367 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨20, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83377119899499 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102777910367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_21 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83342720612627 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (441111971889 / 20000000000000 : ℝ))
      (E := (cell13093 ⟨21, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83342720612627 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (441111971889 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_22 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83308345448907 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102781921697 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨22, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83308345448907 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102781921697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_23 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (8327399437569 / 10000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (220556783421 / 10000000000000 : ℝ))
      (E := (cell13093 ⟨23, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (8327399437569 / 10000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (220556783421 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_24 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (41619833680247 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102785946691 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨24, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (41619833680247 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102785946691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_25 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (16641072874201 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551393976739 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨25, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (16641072874201 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551393976739 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_26 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83171085375073 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551394969369 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨26, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83171085375073 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551394969369 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_27 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83136830340713 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (137848995263 / 6250000000000 : ℝ))
      (E := (cell13093 ⟨27, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83136830340713 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (137848995263 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_28 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83102599236103 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205587932367 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨28, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83102599236103 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205587932367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_29 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (5191774501849 / 6250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102795981163 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨29, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (5191774501849 / 6250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102795981163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_30 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (83034208689657 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (88223838289 / 4000000000000 : ℝ))
      (E := (cell13093 ⟨30, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (83034208689657 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (88223838289 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_31 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (10375006148123 / 12500000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551399994257 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨31, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (10375006148123 / 12500000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551399994257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_32 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82965913484389 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205603964371 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨32, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82965913484389 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205603964371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_33 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82931801556849 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205607978813 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨33, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82931801556849 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205607978813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_34 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (5181107085719 / 6250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (441122404227 / 20000000000000 : ℝ))
      (E := (cell13093 ⟨34, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (5181107085719 / 6250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (441122404227 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_35 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82863648897647 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205616033227 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨35, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82863648897647 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205616033227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_36 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (10353701013091 / 12500000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205620015353 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨36, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (10353701013091 / 12500000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205620015353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_37 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82795590962351 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205624026267 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨37, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82795590962351 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205624026267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_38 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (41380798720137 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205628065859 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨38, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (41380798720137 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205628065859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_39 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (10340953438551 / 12500000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551408018759 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨39, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (10340953438551 / 12500000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551408018759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13094_20 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83377105792341 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205443634377 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨20, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83377105792341 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205443634377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_21 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (20835676627919 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205447669661 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨21, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (20835676627919 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205447669661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_22 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83308331354159 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551362912557 / 25000000000000 : ℝ))
      (E := (cell13094 ⟨22, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83308331354159 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551362912557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_23 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83273980287139 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441091139219 / 20000000000000 : ℝ))
      (E := (cell13094 ⟨23, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83273980287139 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441091139219 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_24 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (16647930655627 / 20000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (275682461699 / 12500000000000 : ℝ))
      (E := (cell13094 ⟨24, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (16647930655627 / 20000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (275682461699 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_25 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (5200334393427 / 6250000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (88218548157 / 4000000000000 : ℝ))
      (E := (cell13094 ⟨25, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (5200334393427 / 6250000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (88218548157 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_26 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83171071305081 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102733864853 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨26, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83171071305081 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102733864853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_27 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83136816276897 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102735857417 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨27, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83136816276897 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102735857417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_28 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41551292589229 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205475778393 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨28, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41551292589229 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205475778393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_29 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (10383547247263 / 12500000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (275684968349 / 12500000000000 : ℝ))
      (E := (cell13094 ⟨29, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (10383547247263 / 12500000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (275684968349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_30 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (83034194644337 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (137842737327 / 6250000000000 : ℝ))
      (E := (cell13094 ⟨30, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (83034194644337 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (137842737327 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_31 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (4150001757291 / 5000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441097562819 / 20000000000000 : ℝ))
      (E := (cell13094 ⟨31, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (4150001757291 / 5000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441097562819 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_32 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41482949725687 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441098359709 / 20000000000000 : ℝ))
      (E := (cell13094 ⟨32, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41482949725687 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441098359709 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_33 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82931787529979 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (110274790507 / 5000000000000 : ℝ))
      (E := (cell13094 ⟨33, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82931787529979 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (110274790507 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_34 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41448849675387 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (110274992483 / 5000000000000 : ℝ))
      (E := (cell13094 ⟨34, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41448849675387 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (110274992483 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_35 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (20715908720763 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205503858997 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨35, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (20715908720763 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205503858997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_36 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41414797048131 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102753919207 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨36, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41414797048131 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102753919207 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_37 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82795576960009 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205511846667 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨37, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82795576960009 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205511846667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_38 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (20690395861013 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205515883643 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨38, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (20690395861013 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205515883643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_39 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (827276135183 / 1000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (8822079561 / 400000000000 : ℝ))
      (E := (cell13094 ⟨39, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (827276135183 / 1000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (8822079561 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13095_20 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (4168854584367 / 5000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205331502071 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨20, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (4168854584367 / 5000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205331502071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_21 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41671346206441 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205335533951 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨21, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41671346206441 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205335533951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_22 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41654158630783 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102669755581 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨22, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41654158630783 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102669755581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_23 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41636983100371 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205343553719 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨23, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41636983100371 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205343553719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_24 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83239639197929 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205347547951 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨24, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83239639197929 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205347547951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_25 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83205336220811 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551337888767 / 25000000000000 : ℝ))
      (E := (cell13095 ⟨25, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83205336220811 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551337888767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_26 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (83171057237241 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205355577677 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨26, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (83171057237241 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205355577677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_27 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (1299012534613 / 1562500000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205359618159 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨27, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (1299012534613 / 1562500000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205359618159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_28 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41551285561481 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205363620161 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨28, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41551285561481 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205363620161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_29 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (20767090982193 / 25000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275670955507 / 12500000000000 : ℝ))
      (E := (cell13095 ⟨29, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (20767090982193 / 25000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275670955507 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_30 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16606836120233 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205371632983 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨30, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16606836120233 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205371632983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_31 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41500010554401 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205375646907 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨31, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41500010554401 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205375646907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_32 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16593177084101 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (137836226779 / 6250000000000 : ℝ))
      (E := (cell13095 ⟨32, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16593177084101 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (137836226779 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_33 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16586354701051 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275672961979 / 12500000000000 : ℝ))
      (E := (cell13095 ⟨33, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16586354701051 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275672961979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_34 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (20724421333047 / 25000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205387673933 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨34, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (20724421333047 / 25000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205387673933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_35 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82863620870599 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551347920129 / 25000000000000 : ℝ))
      (E := (cell13095 ⟨35, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82863620870599 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551347920129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_36 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41414790044969 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205395715917 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨36, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41414790044969 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205395715917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_37 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82795562959809 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205399721531 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨37, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82795562959809 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205399721531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_38 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82761569449969 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551350938979 / 25000000000000 : ℝ))
      (E := (cell13095 ⟨38, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82761569449969 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551350938979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_39 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82727599530331 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205407759977 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨39, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82727599530331 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205407759977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13096_20 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (16675415516899 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205219365503 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨20, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (16675415516899 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205219365503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_21 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83342678316243 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (110261169699 / 5000000000000 : ℝ))
      (E := (cell13096 ⟨21, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83342678316243 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (110261169699 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_22 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (10413537896391 / 12500000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205227426197 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨22, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (10413537896391 / 12500000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205227426197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_23 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83273952116499 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102615703541 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨23, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83273952116499 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102615703541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_24 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (665917000959 / 800000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102617728231 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨24, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (665917000959 / 800000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102617728231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_25 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83205322148943 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205239460383 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨25, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83205322148943 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205239460383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_26 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83171043171551 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205243479847 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨26, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83171043171551 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205243479847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_27 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (20784197038929 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205247458749 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨27, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (20784197038929 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205247458749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_28 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (16620511413923 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102625728837 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨28, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (16620511413923 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102625728837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_29 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (8306834988159 / 10000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205255478537 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨29, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (8306834988159 / 10000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205255478537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_30 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (4151708328007 / 5000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205259523031 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨30, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (4151708328007 / 5000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205259523031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_31 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (83000007073931 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205263534039 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨31, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (83000007073931 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205263534039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_32 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41482935695891 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (275658439091 / 12500000000000 : ℝ))
      (E := (cell13096 ⟨32, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41482935695891 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (275658439091 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_33 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41465879741337 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102635759327 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨33, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41465879741337 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102635759327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_34 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (16579534263149 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205275552599 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨34, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (16579534263149 / 20000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205275552599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_35 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82863606860289 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205279556453 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨35, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82863606860289 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205279556453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_36 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (20707391521439 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205283589169 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨36, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (20707391521439 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205283589169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_37 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82795548961749 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205287592147 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨37, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82795548961749 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205287592147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_38 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82761555458027 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205291623941 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨38, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82761555458027 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205291623941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_39 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82727585544501 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102647812729 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨39, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82727585544501 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102647812729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13097_20 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83377063483807 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205107282987 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨20, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83377063483807 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205107282987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_21 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (260445825693 / 312500000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102555654043 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨21, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (260445825693 / 312500000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102555654043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_22 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (20827072270711 / 25000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (137819704913 / 6250000000000 : ℝ))
      (E := (cell13097 ⟨22, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (20827072270711 / 25000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (137819704913 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_23 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83273938034409 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205119314571 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨23, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83273938034409 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205119314571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_24 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (3329584441759 / 4000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205123302301 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨24, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (3329584441759 / 4000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205123302301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_25 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41602654039613 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205127361441 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨25, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41602654039613 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205127361441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_26 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83171029108013 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102565688879 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨26, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83171029108013 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102565688879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_27 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83136774098351 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205135353561 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨27, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83136774098351 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205135353561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_28 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41551271509209 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (275642418679 / 12500000000000 : ℝ))
      (E := (cell13097 ⟨28, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41551271509209 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (275642418679 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_29 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41534167918277 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (220514336729 / 10000000000000 : ℝ))
      (E := (cell13097 ⟨29, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41534167918277 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (220514336729 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_30 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (83034152521263 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102573704411 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨30, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (83034152521263 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102573704411 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_31 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (16599998608241 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102575708459 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨31, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (16599998608241 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102575708459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_32 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (20741464341301 / 25000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (441031090267 / 20000000000000 : ℝ))
      (E := (cell13097 ⟨32, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (20741464341301 / 25000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (441031090267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_33 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41465872731119 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (8613904119 / 390625000000 : ℝ))
      (E := (cell13097 ⟨33, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41465872731119 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (8613904119 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_34 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41448828650723 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205163427013 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨34, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41448828650723 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205163427013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_35 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82863592852121 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102583743403 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨35, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82863592852121 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102583743403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_36 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41414776041857 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102585729087 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨36, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41414776041857 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102585729087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_37 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82795534965829 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205175517229 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨37, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82795534965829 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205175517229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_38 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (1293149085441 / 1562500000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102589743859 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨38, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (1293149085441 / 1562500000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102589743859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_39 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82727571560809 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205183545453 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨39, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82727571560809 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205183545453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13098_20 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (3335081975411 / 4000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204995196209 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨20, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (3335081975411 / 4000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204995196209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_21 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (10417831266179 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204999217931 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨21, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (10417831266179 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2204999217931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_22 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41654137498357 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102501621743 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨22, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41654137498357 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102501621743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_23 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (10409240494309 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205007217801 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨23, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (10409240494309 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205007217801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_24 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41619798485113 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205011260703 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨24, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41619798485113 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205011260703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_25 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (4160264700583 / 5000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205015258241 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨25, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (4160264700583 / 5000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205015258241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_26 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (2599094220207 / 3125000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102509635707 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨26, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (2599094220207 / 3125000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102509635707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_27 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41568380021567 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102511651299 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨27, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41568380021567 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102511651299 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_28 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (10387816121171 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205027295441 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨28, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (10387816121171 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205027295441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_29 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (83068321793667 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441006262063 / 20000000000000 : ℝ))
      (E := (cell13098 ⟨29, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (83068321793667 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441006262063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_30 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (83034138484531 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205035290363 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨30, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (83034138484531 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205035290363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_31 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (132799966417 / 160000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102519677059 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨31, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (132799966417 / 160000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102519677059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_32 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (8296584334077 / 10000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (275630415887 / 12500000000000 : ℝ))
      (E := (cell13098 ⟨32, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (8296584334077 / 10000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (275630415887 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_33 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (16586346288789 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (275630923253 / 12500000000000 : ℝ))
      (E := (cell13098 ⟨33, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (16586346288789 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (275630923253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_34 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82897643289289 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205051355823 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨34, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82897643289289 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205051355823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_35 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (16572715769219 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (137815963307 / 6250000000000 : ℝ))
      (E := (cell13098 ⟨35, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (16572715769219 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (137815963307 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_36 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41414769041907 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205059381621 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨36, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41414769041907 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205059381621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_37 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82795520972049 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441012687613 / 20000000000000 : ℝ))
      (E := (cell13098 ⟨37, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82795520972049 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441012687613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_38 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (1034519093507 / 1250000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551266851497 / 25000000000000 : ℝ))
      (E := (cell13098 ⟨38, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (1034519093507 / 1250000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551266851497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_39 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (16545511515851 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205071461203 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨39, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (16545511515851 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205071461203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13099_20 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41688517644449 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551220776293 / 25000000000000 : ℝ))
      (E := (cell13099 ⟨20, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41688517644449 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551220776293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_21 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41671318019629 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551221780879 / 25000000000000 : ℝ))
      (E := (cell13099 ⟨21, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41671318019629 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551221780879 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_22 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41654130456369 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204891145741 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨22, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41654130456369 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204891145741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_23 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (5204619367293 / 6250000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (55122379379 / 2500000000000 : ℝ))
      (E := (cell13099 ⟨23, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (5204619367293 / 6250000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (55122379379 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_24 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (83239582898629 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102449578219 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨24, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (83239582898629 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102449578219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_25 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (20801319986561 / 25000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (110245160461 / 5000000000000 : ℝ))
      (E := (cell13099 ⟨25, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (20801319986561 / 25000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (110245160461 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_26 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (16634200197477 / 20000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204907219271 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨26, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (16634200197477 / 20000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204907219271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_27 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41568372995033 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204911188901 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨27, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41568372995033 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204911188901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_28 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41551257461233 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551228809299 / 25000000000000 : ℝ))
      (E := (cell13099 ⟨28, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41551257461233 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551228809299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_29 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (3322732310117 / 4000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (220491924909 / 10000000000000 : ℝ))
      (E := (cell13099 ⟨29, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (3322732310117 / 4000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (220491924909 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_30 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41517062224973 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204923226201 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨30, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41517062224973 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204923226201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_31 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (8299996498219 / 10000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551231821767 / 25000000000000 : ℝ))
      (E := (cell13099 ⟨31, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (8299996498219 / 10000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551231821767 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_32 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (1037072866481 / 1250000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204931257203 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨32, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (1037072866481 / 1250000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204931257203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_33 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (16586343485559 / 20000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (275616914167 / 12500000000000 : ℝ))
      (E := (cell13099 ⟨33, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (16586343485559 / 20000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (275616914167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_34 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41448814639637 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (440987856077 / 20000000000000 : ℝ))
      (E := (cell13099 ⟨34, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41448814639637 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (440987856077 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_35 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (8286356484221 / 10000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (220494333477 / 10000000000000 : ℝ))
      (E := (cell13099 ⟨35, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (8286356484221 / 10000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (220494333477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_36 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41414762043027 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (275618419939 / 12500000000000 : ℝ))
      (E := (cell13099 ⟨36, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41414762043027 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (275618419939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_37 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82795506980409 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102475677327 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨37, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82795506980409 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102475677327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_38 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41380756747517 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204955378751 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨38, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41380756747517 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204955378751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_39 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82727543599839 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (220495937271 / 10000000000000 : ℝ))
      (E := (cell13099 ⟨39, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82727543599839 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (220495937271 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

end BstLean.Part268
