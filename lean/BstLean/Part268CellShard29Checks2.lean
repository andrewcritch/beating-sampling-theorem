import BstLean.Part268CellShard29Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13075_40 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20673483303759 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207658812159 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨40, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20673483303759 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207658812159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_41 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41330005131947 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551915701201 / 25000000000000 : ℝ))
      (E := (cell13075 ⟨41, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41330005131947 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551915701201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_42 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (82626110813693 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (220766682251 / 10000000000000 : ℝ))
      (E := (cell13075 ⟨42, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (82626110813693 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (220766682251 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_43 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (16518446966989 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207670805217 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨43, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (16518446966989 / 20000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207670805217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_44 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (8255838229831 / 10000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551918702577 / 25000000000000 : ℝ))
      (E := (cell13075 ⟨44, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (8255838229831 / 10000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551918702577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_45 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41262276587299 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207678836141 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨45, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41262276587299 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207678836141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_46 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41245373717381 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207682880863 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨46, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41245373717381 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207682880863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_47 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (5153560315619 / 6250000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207686883457 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨47, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (5153560315619 / 6250000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207686883457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_48 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20605801497817 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207690900541 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨48, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20605801497817 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207690900541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_49 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (82389470230243 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (110384746481 / 5000000000000 : ℝ))
      (E := (cell13075 ⟨49, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (82389470230243 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (110384746481 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_50 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (82355757738363 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207698908967 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨50, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (82355757738363 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207698908967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_51 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41161034243651 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551925738419 / 25000000000000 : ℝ))
      (E := (cell13075 ⟨51, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41161034243651 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (551925738419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_52 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20572100612219 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207706942559 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨52, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20572100612219 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207706942559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_53 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (82254759595041 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (137981936899 / 6250000000000 : ℝ))
      (E := (cell13075 ⟨53, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (82254759595041 / 100000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (137981936899 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_54 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (10277642487237 / 12500000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (44154299509 / 2000000000000 : ℝ))
      (E := (cell13075 ⟨54, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (10277642487237 / 12500000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (44154299509 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_55 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20546885832419 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (11038595061 / 500000000000 : ℝ))
      (E := (cell13075 ⟨55, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20546885832419 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (11038595061 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_56 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (41076984931377 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441544607517 / 20000000000000 : ℝ))
      (E := (cell13075 ⟨56, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (41076984931377 / 50000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (441544607517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_57 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (20530104867411 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (275965880929 / 12500000000000 : ℝ))
      (E := (cell13075 ⟨57, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (20530104867411 / 25000000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (275965880929 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_58 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (5130430757687 / 6250000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207731037369 / 100000000000000 : ℝ))
      (E := (cell13075 ⟨58, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (5130430757687 / 6250000000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (2207731037369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13075_59 : CellCertificate 13075 (438251359323323 / 5000000000000000 : ℝ) (321288422682783 / 200000000000000000 : ℝ) (324273195115237 / 10000000000000000 : ℝ)
    (cell13075 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · norm_num [cell13075]
  · have h := gap_lower (n := 13075) (a := (641042092153 / 781250000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (1103867531021 / 50000000000000 : ℝ))
      (E := (cell13075 ⟨59, by decide⟩).energy) (xi := (324273195115237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13075 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13075]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13075])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13075) (a := (641042092153 / 781250000000 : ℝ)) (b := (157483361619 / 100000000000000 : ℝ)) (q := (1103867531021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13075])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13075]

theorem cert13076_40 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (4134695959623 / 5000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (275943278901 / 12500000000000 : ℝ))
      (E := (cell13076 ⟨40, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (4134695959623 / 5000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (275943278901 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_41 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (1033249953093 / 1250000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551887555293 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨41, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (1033249953093 / 1250000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551887555293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_42 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41313048401677 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (441510847249 / 20000000000000 : ℝ))
      (E := (cell13076 ⟨42, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41313048401677 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (441510847249 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_43 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82592220830717 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (137972392201 / 6250000000000 : ℝ))
      (E := (cell13076 ⟨43, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82592220830717 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (137972392201 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_44 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82558368300189 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207562277787 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨44, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82558368300189 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207562277787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_45 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41262269591289 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551891575287 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨45, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41262269591289 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551891575287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_46 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41245366724419 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (55189257113 / 2500000000000 : ℝ))
      (E := (cell13076 ⟨46, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41245366724419 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (55189257113 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_47 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82456951070071 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207574343657 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨47, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82456951070071 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207574343657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_48 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82423192017521 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207578358407 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨48, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82423192017521 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207578358407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_49 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41194728131289 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207582326203 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨49, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41194728131289 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207582326203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_50 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41177871888387 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103793181151 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨50, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41177871888387 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103793181151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_51 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (16464410906357 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103795202407 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨51, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (16464410906357 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103795202407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_52 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (3291535539977 / 4000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207594391547 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨52, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (3291535539977 / 4000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207594391547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_53 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82254745651653 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207598437267 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨53, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82254745651653 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207598437267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_54 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (16444225192113 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103801210137 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨54, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (16444225192113 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103801210137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_55 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82187529398397 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551901613753 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨55, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82187529398397 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551901613753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_56 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82153955937523 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207610478429 / 100000000000000 : ℝ))
      (E := (cell13076 ⟨56, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82153955937523 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (2207610478429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_57 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (16424081110091 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551903621589 / 25000000000000 : ℝ))
      (E := (cell13076 ⟨57, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (16424081110091 / 20000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (551903621589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_58 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (82086878209841 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103809237209 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨58, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (82086878209841 / 100000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103809237209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13076_59 : CellCertificate 13076 (109559537506591 / 1250000000000000 : ℝ) (1606319219936347 / 1000000000000000000 : ℝ) (81061956112713 / 2500000000000000 : ℝ)
    (cell13076 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · norm_num [cell13076]
  · have h := gap_lower (n := 13076) (a := (41026686944233 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103811248631 / 50000000000000 : ℝ))
      (E := (cell13076 ⟨59, by decide⟩).energy) (xi := (81061956112713 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13076 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13076]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13076])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13076) (a := (41026686944233 / 50000000000000 : ℝ)) (b := (1230243587 / 781250000000 : ℝ)) (q := (1103811248631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13076])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13076]

theorem cert13077_40 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (1292092268313 / 1562500000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103716852387 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨40, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (1292092268313 / 1562500000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103716852387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_41 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (20664995558283 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207437692081 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨41, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (20664995558283 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207437692081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_42 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (82626082795161 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (68982553267 / 3125000000000 : ℝ))
      (E := (cell13077 ⟨42, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (82626082795161 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (68982553267 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_43 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41296103414317 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207445740951 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨43, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41296103414317 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207445740951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_44 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (82558354304211 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441489948201 / 20000000000000 : ℝ))
      (E := (cell13077 ⟨44, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (82558354304211 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441489948201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_45 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (825245251927 / 1000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207453761893 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨45, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (825245251927 / 1000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207453761893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_46 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (2577834983283 / 3125000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207457801763 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨46, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (2577834983283 / 3125000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207457801763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_47 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (82456937092379 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207461799597 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨47, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (82456937092379 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207461799597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_48 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41211589022957 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207465812013 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨48, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41211589022957 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207465812013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_49 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (20597360574263 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441493967303 / 20000000000000 : ℝ))
      (E := (cell13077 ⟨49, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (20597360574263 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441493967303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_50 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (20588932454331 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103736905689 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨50, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (20588932454331 / 25000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103736905689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_51 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (16464408115681 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441495570339 / 20000000000000 : ℝ))
      (E := (cell13077 ⟨51, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (16464408115681 / 20000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441495570339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_52 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (82288374552111 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103740918139 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨52, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (82288374552111 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103740918139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_53 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (51409207319 / 62500000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103742939947 / 50000000000000 : ℝ))
      (E := (cell13077 ⟨53, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (51409207319 / 62500000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (1103742939947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_54 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (10277639003171 / 12500000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441497983991 / 20000000000000 : ℝ))
      (E := (cell13077 ⟨54, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (10277639003171 / 12500000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (441497983991 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_55 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (82187515469251 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (220749389357 / 10000000000000 : ℝ))
      (E := (cell13077 ⟨55, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (82187515469251 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (220749389357 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_56 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (10269242751803 / 12500000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207497915021 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨56, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (10269242751803 / 12500000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207497915021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_57 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41060195816699 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551875480257 / 25000000000000 : ℝ))
      (E := (cell13077 ⟨57, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41060195816699 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (551875480257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_58 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (82086864298821 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207505966421 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨58, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (82086864298821 / 100000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207505966421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13077_59 : CellCertificate 13077 (876449885327189 / 10000000000000000 : ℝ) (1606196345260141 / 1000000000000000000 : ℝ) (162111228893121 / 5000000000000000 : ℝ)
    (cell13077 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · norm_num [cell13077]
  · have h := gap_lower (n := 13077) (a := (41026679991739 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207509987459 / 100000000000000 : ℝ))
      (E := (cell13077 ⟨59, by decide⟩).energy) (xi := (162111228893121 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13077 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13077]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13077])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13077) (a := (41026679991739 / 50000000000000 : ℝ)) (b := (78729499273 / 50000000000000 : ℝ)) (q := (2207509987459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13077])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13077]

theorem cert13078_40 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82693891153751 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103660587037 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨40, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82693891153751 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103660587037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_41 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82659968220969 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103662608767 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨41, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82659968220969 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103662608767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_42 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (41313034394557 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207329227409 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨42, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (41313034394557 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207329227409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_43 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (10324024103587 / 12500000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (275916650303 / 12500000000000 : ℝ))
      (E := (cell13078 ⟨43, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (10324024103587 / 12500000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (275916650303 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_44 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82558340310377 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207337258837 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨44, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82558340310377 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207337258837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_45 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (16504902240993 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207341277279 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨45, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (16504902240993 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207341277279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_46 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (16498141096683 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207345255823 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨46, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (16498141096683 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207345255823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_47 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82456923116827 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207349251279 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨47, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82456923116827 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207349251279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_48 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82423164076447 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (551838330083 / 25000000000000 : ℝ))
      (E := (cell13078 ⟨48, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82423164076447 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (551838330083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_49 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (2574669635427 / 3125000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207357283577 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨49, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (2574669635427 / 3125000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207357283577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_50 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82355715860011 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (137960082201 / 6250000000000 : ℝ))
      (E := (cell13078 ⟨50, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82355715860011 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (137960082201 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_51 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82322026627161 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103682676681 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨51, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82322026627161 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103682676681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_52 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82288360606933 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207369335819 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨52, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82288360606933 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207369335819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_53 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82254717771281 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207373377357 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨53, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82254717771281 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207373377357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_54 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (16444219618461 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (137961084767 / 6250000000000 : ℝ))
      (E := (cell13078 ⟨54, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (16444219618461 / 20000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (137961084767 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_55 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (41093750771119 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207381387011 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨55, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (41093750771119 / 50000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207381387011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_56 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82153928093457 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (55184635163 / 2500000000000 : ℝ))
      (E := (cell13078 ⟨56, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82153928093457 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (55184635163 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_57 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82120377718471 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (275923676329 / 12500000000000 : ℝ))
      (E := (cell13078 ⟨57, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82120377718471 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (275923676329 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_58 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (82086850389931 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103696727087 / 50000000000000 : ℝ))
      (E := (cell13078 ⟨58, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (82086850389931 / 100000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (1103696727087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13078_59 : CellCertificate 13078 (876423474469139 / 10000000000000000 : ℝ) (200759186172623 / 125000000000000000 : ℝ) (40524636890051 / 1250000000000000 : ℝ)
    (cell13078 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · norm_num [cell13078]
  · have h := gap_lower (n := 13078) (a := (4102667304031 / 5000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207397473409 / 100000000000000 : ℝ))
      (E := (cell13078 ⟨59, by decide⟩).energy) (xi := (40524636890051 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13078 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13078]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13078])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13078) (a := (4102667304031 / 5000000000000 : ℝ)) (b := (157446819847 / 100000000000000 : ℝ)) (q := (2207397473409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13078])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13078]

theorem cert13079_40 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (5168367321101 / 6250000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441441739579 / 20000000000000 : ℝ))
      (E := (cell13079 ⟨40, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (5168367321101 / 6250000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441441739579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_41 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82659954210953 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551803169979 / 25000000000000 : ℝ))
      (E := (cell13079 ⟨41, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82659954210953 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (551803169979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_42 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (8262605478521 / 10000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103608373007 / 50000000000000 : ℝ))
      (E := (cell13079 ⟨42, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (8262605478521 / 10000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (1103608373007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_43 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (825921788309 / 1000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (220722071849 / 10000000000000 : ℝ))
      (E := (cell13079 ⟨43, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (825921788309 / 1000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (220722071849 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_44 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16511665263737 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (220722477241 / 10000000000000 : ℝ))
      (E := (cell13079 ⟨44, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16511665263737 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (220722477241 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_45 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82524497219371 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441445757681 / 20000000000000 : ℝ))
      (E := (cell13079 ⟨45, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82524497219371 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441445757681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_46 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41245345751957 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (44144655291 / 2000000000000 : ℝ))
      (E := (cell13079 ⟨46, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41245345751957 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (44144655291 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_47 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (16491381828683 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207236816597 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨47, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (16491381828683 / 20000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207236816597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_48 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82423150109119 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441448164879 / 20000000000000 : ℝ))
      (E := (cell13079 ⟨48, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82423150109119 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (441448164879 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_49 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41194707186207 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207244844371 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨49, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41194707186207 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207244844371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_50 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41177850952417 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207248814801 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨50, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41177850952417 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207248814801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_51 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41161006339027 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (88290114031 / 4000000000000 : ℝ))
      (E := (cell13079 ⟨51, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41161006339027 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (88290114031 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_52 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82288346663889 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207256890173 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨52, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82288346663889 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207256890173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_53 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82254703834297 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207260870567 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨53, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82254703834297 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207260870567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_54 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (657768673291 / 800000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207264906561 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨54, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (657768673291 / 800000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207264906561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_55 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (41093743808679 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207268935337 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨55, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (41093743808679 / 50000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207268935337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_56 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82153914174621 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207272952929 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨56, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82153914174621 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207272952929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_57 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (20530090951419 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207276955169 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨57, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (20530090951419 / 25000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207276955169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_58 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (8208683648317 / 10000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207280937681 / 100000000000000 : ℝ))
      (E := (cell13079 ⟨58, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (8208683648317 / 10000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (2207280937681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13079_59 : CellCertificate 13079 (175279413495537 / 2000000000000000 : ℝ) (802975326147281 / 500000000000000000 : ℝ) (81042934113087 / 2500000000000000 : ℝ)
    (cell13079 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · norm_num [cell13079]
  · have h := gap_lower (n := 13079) (a := (82053332179889 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (275910619389 / 12500000000000 : ℝ))
      (E := (cell13079 ⟨59, by decide⟩).energy) (xi := (81042934113087 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13079 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13079]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13079])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13079) (a := (82053332179889 / 100000000000000 : ℝ)) (b := (157434643039 / 100000000000000 : ℝ)) (q := (275910619389 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13079])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13079]

theorem cert13080_40 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82693863123627 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207096217453 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨40, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82693863123627 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207096217453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_41 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82659940203081 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207100255651 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨41, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82659940203081 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207100255651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_42 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (1652520815669 / 2000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103552130179 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨42, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (1652520815669 / 2000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103552130179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_43 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (5162010302203 / 6250000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207108289149 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨43, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (5162010302203 / 6250000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207108289149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_44 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (16511662465827 / 20000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551778070431 / 25000000000000 : ℝ))
      (E := (cell13080 ⟨44, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (16511662465827 / 20000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551778070431 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_45 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41262241617959 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207116295273 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨45, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41262241617959 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207116295273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_46 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41245338763277 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207120327941 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨46, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41245338763277 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207120327941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_47 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41228447586071 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (275890539839 / 12500000000000 : ℝ))
      (E := (cell13080 ⟨47, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41228447586071 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (275890539839 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_48 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (10302892017991 / 12500000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103564162101 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨48, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (10302892017991 / 12500000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103564162101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_49 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41194700206651 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551783085479 / 25000000000000 : ℝ))
      (E := (cell13080 ⟨49, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41194700206651 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (551783085479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_50 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (16471137590359 / 20000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207136369147 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨50, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (16471137590359 / 20000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207136369147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_51 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41160999365541 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207140402977 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨51, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41160999365541 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207140402977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_52 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82288332722981 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207144381209 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨52, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82288332722981 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207144381209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_53 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82254689899447 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207148418613 / 100000000000000 : ℝ))
      (E := (cell13080 ⟨53, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82254689899447 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (2207148418613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_54 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (41110535116289 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (11035762263 / 500000000000 : ℝ))
      (E := (cell13080 ⟨54, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (41110535116289 / 50000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (11035762263 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_55 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82187473694609 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103578210139 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨55, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82187473694609 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103578210139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_56 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (20538475064479 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (220716043593 / 10000000000000 : ℝ))
      (E := (cell13080 ⟨56, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (20538475064479 / 25000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (220716043593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_57 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (8212034989501 / 10000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103582247729 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨57, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (8212034989501 / 10000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103582247729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_58 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82086822578539 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (441433695229 / 20000000000000 : ℝ))
      (E := (cell13080 ⟨58, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82086822578539 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (441433695229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13080_59 : CellCertificate 13080 (876370664351939 / 10000000000000000 : ℝ) (401456958499141 / 250000000000000000 : ℝ) (162073190890531 / 5000000000000000 : ℝ)
    (cell13080 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · norm_num [cell13080]
  · have h := gap_lower (n := 13080) (a := (82053318281287 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103586245899 / 50000000000000 : ℝ))
      (E := (cell13080 ⟨59, by decide⟩).energy) (xi := (162073190890531 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13080 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13080]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13080])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13080) (a := (82053318281287 / 100000000000000 : ℝ)) (b := (78711234061 / 50000000000000 : ℝ)) (q := (1103586245899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13080])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13080]

theorem cert13081_40 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (82693849111783 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (551745947883 / 25000000000000 : ℝ))
      (E := (cell13081 ⟨40, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (82693849111783 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (551745947883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_41 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (82659926197353 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103493884159 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨41, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (82659926197353 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103493884159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_42 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41313013391917 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (275873978659 / 12500000000000 : ℝ))
      (E := (cell13081 ⟨42, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41313013391917 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (275873978659 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_43 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41296075420869 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (275874474587 / 12500000000000 : ℝ))
      (E := (cell13081 ⟨43, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41296075420869 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (275874474587 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_44 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41279149170863 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206999845657 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨44, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41279149170863 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2206999845657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_45 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41262234627303 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441400771357 / 20000000000000 : ℝ))
      (E := (cell13081 ⟨45, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41262234627303 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (441400771357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_46 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41245331775667 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207007887077 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨46, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41245331775667 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207007887077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_47 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (1288388768797 / 1562500000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103505937759 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨47, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (1288388768797 / 1562500000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103505937759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_48 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (20605780545219 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (88280635149 / 4000000000000 : ℝ))
      (E := (cell13081 ⟨48, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (20605780545219 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (88280635149 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_49 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41194693228163 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103509947101 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨49, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41194693228163 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103509947101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_50 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (82355674000891 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103511959621 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨50, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (82355674000891 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103511959621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_51 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (16464396957249 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103513975463 / 50000000000000 : ℝ))
      (E := (cell13081 ⟨51, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (16464396957249 / 20000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (1103513975463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_52 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41144159392103 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207031927059 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨52, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41144159392103 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207031927059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_53 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (82254675966729 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220703596241 / 10000000000000 : ℝ))
      (E := (cell13081 ⟨53, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (82254675966729 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (220703596241 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_54 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (82221056305913 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207039994389 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨54, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (82221056305913 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207039994389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_55 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (10273432471749 / 12500000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207044019241 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨55, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (10273432471749 / 12500000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207044019241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_56 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41076943171671 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207048033001 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨56, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41076943171671 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207048033001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_57 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (41060167993237 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (4414104063 / 200000000000 : ℝ))
      (E := (cell13081 ⟨57, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (41060167993237 / 50000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (4414104063 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_58 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (20521702169009 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207056069569 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨58, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (20521702169009 / 25000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207056069569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13081_59 : CellCertificate 13081 (87634426509101 / 1000000000000000 : ℝ) (1605705034482679 / 1000000000000000000 : ℝ) (20257564444097 / 625000000000000 : ℝ)
    (cell13081 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · norm_num [cell13081]
  · have h := gap_lower (n := 13081) (a := (82053304384813 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207060083467 / 100000000000000 : ℝ))
      (E := (cell13081 ⟨59, by decide⟩).energy) (xi := (20257564444097 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13081 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13081]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13081])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13081) (a := (82053304384813 / 100000000000000 : ℝ)) (b := (31482059019 / 20000000000000 : ℝ)) (q := (2207060083467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13081])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13081]

theorem cert13082_40 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20673458775521 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (44137427227 / 2000000000000 : ℝ))
      (E := (cell13082 ⟨40, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20673458775521 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (44137427227 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_41 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (8265991219377 / 10000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (220687533553 / 10000000000000 : ℝ))
      (E := (cell13082 ⟨41, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (8265991219377 / 10000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (220687533553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_42 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82626012786361 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (88275175757 / 4000000000000 : ℝ))
      (E := (cell13082 ⟨42, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82626012786361 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (88275175757 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_43 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82592136850371 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (220688341769 / 10000000000000 : ℝ))
      (E := (cell13082 ⟨43, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82592136850371 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (220688341769 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_44 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82558284356459 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206887405331 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨44, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82558284356459 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206887405331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_45 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (16504891055087 / 20000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103445707019 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨45, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (16504891055087 / 20000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103445707019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_46 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (20622662394563 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206895441957 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨46, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (20622662394563 / 25000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206895441957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_47 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82456867236013 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551724857017 / 25000000000000 : ℝ))
      (E := (cell13082 ⟨47, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82456867236013 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551724857017 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_48 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82423108219961 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551725871991 / 25000000000000 : ℝ))
      (E := (cell13082 ⟨48, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82423108219961 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551725871991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_49 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82389372501487 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551726875307 / 25000000000000 : ℝ))
      (E := (cell13082 ⟨49, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82389372501487 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551726875307 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_50 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82355660052123 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206911465083 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨50, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82355660052123 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206911465083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_51 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82321970843543 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206915494623 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨51, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82321970843543 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206915494623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_52 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (16457660969513 / 20000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103459763861 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨52, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (16457660969513 / 20000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103459763861 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_53 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (16450932407229 / 20000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551730890261 / 25000000000000 : ℝ))
      (E := (cell13082 ⟨53, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (16450932407229 / 20000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (551730890261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_54 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (4111052119069 / 5000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (275865941491 / 12500000000000 : ℝ))
      (E := (cell13082 ⟨54, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (4111052119069 / 5000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (275865941491 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_55 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (41093722927753 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206931554819 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨55, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (41093722927753 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206931554819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_56 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (41076936215449 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (275866945833 / 12500000000000 : ℝ))
      (E := (cell13082 ⟨56, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (41076936215449 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (275866945833 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_57 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (41060161040033 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103469811239 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨57, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (41060161040033 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103469811239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_58 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (82086794775661 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206943599541 / 100000000000000 : ℝ))
      (E := (cell13082 ⟨58, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (82086794775661 / 100000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (2206943599541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13082_59 : CellCertificate 13082 (438158934847003 / 5000000000000000 : ℝ) (802791126874299 / 500000000000000000 : ℝ) (20255980276551 / 625000000000000 : ℝ)
    (cell13082 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · norm_num [cell13082]
  · have h := gap_lower (n := 13082) (a := (41026645245233 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103473805831 / 50000000000000 : ℝ))
      (E := (cell13082 ⟨59, by decide⟩).energy) (xi := (20255980276551 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13082 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13082]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13082])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13082) (a := (41026645245233 / 50000000000000 : ℝ)) (b := (157398123959 / 100000000000000 : ℝ)) (q := (1103473805831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13082])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13082]

theorem cert13083_40 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (82693821094529 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (220675892691 / 10000000000000 : ℝ))
      (E := (cell13083 ⟨40, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (82693821094529 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (220675892691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_41 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (8265989819233 / 10000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551690739323 / 25000000000000 : ℝ))
      (E := (cell13083 ⟨41, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (8265989819233 / 10000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551690739323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_42 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (82625998791031 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103383477161 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨42, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (82625998791031 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103383477161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_43 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (16518424572229 / 20000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (88270839023 / 4000000000000 : ℝ))
      (E := (cell13083 ⟨43, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (16518424572229 / 20000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (88270839023 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_44 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (20639567593333 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551693754907 / 25000000000000 : ℝ))
      (E := (cell13083 ⟨44, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (20639567593333 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (551693754907 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_45 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (82524441298403 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103389512969 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨45, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (82524441298403 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103389512969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_46 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (8249063560731 / 10000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103391525753 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨46, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (8249063560731 / 10000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103391525753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_47 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (16491370654231 / 20000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (441357407063 / 20000000000000 : ℝ))
      (E := (cell13083 ⟨47, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (16491370654231 / 20000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (441357407063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_48 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (82423094261183 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206791033981 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨48, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (82423094261183 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206791033981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_49 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (5149334909299 / 6250000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206795045009 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨49, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (5149334909299 / 6250000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206795045009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_50 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (8235564610549 / 10000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206799065693 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨50, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (8235564610549 / 10000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206799065693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_51 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (3292878276119 / 4000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (275850386639 / 12500000000000 : ℝ))
      (E := (cell13083 ⟨51, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (3292878276119 / 4000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (275850386639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_52 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (82288290913057 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103403562069 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨52, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (82288290913057 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103403562069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_53 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (82254648107693 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206811155431 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨53, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (82254648107693 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206811155431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_54 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41110514229489 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206815124333 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨54, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41110514229489 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206815124333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_55 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (1643748638783 / 2000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (275852393161 / 12500000000000 : ℝ))
      (E := (cell13083 ⟨55, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (1643748638783 / 2000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (275852393161 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_56 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (82153858520583 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103411577621 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨56, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (82153858520583 / 100000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103411577621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_57 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (20530077043947 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206827209211 / 100000000000000 : ℝ))
      (E := (cell13083 ⟨57, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (20530077043947 / 25000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (2206827209211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_58 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (41043390438707 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103415621841 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨58, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (41043390438707 / 50000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103415621841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13083_59 : CellCertificate 13083 (21907286954001 / 250000000000000 : ℝ) (802729745895007 / 500000000000000000 : ℝ) (324070341737857 / 10000000000000000 : ℝ)
    (cell13083 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · norm_num [cell13083]
  · have h := gap_lower (n := 13083) (a := (16410655319649 / 20000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103417627037 / 50000000000000 : ℝ))
      (E := (cell13083 ⟨59, by decide⟩).energy) (xi := (324070341737857 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13083 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13083]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13083])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13083) (a := (16410655319649 / 20000000000000 : ℝ)) (b := (157385954711 / 100000000000000 : ℝ)) (q := (1103417627037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13083])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13083]

theorem cert13084_40 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82693807089119 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206646546993 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨40, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82693807089119 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206646546993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_41 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82659884193033 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551662643699 / 25000000000000 : ℝ))
      (E := (cell13084 ⟨41, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82659884193033 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551662643699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_42 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41312992398921 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551663642323 / 25000000000000 : ℝ))
      (E := (cell13084 ⟨42, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41312992398921 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551663642323 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_43 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82592108874059 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103329294029 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨43, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82592108874059 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103329294029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_44 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41279128196173 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551665657417 / 25000000000000 : ℝ))
      (E := (cell13084 ⟨44, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41279128196173 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (551665657417 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_45 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (8252442732351 / 10000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206666633583 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨45, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (8252442732351 / 10000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206666633583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_46 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41245310819253 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103335328401 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨46, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41245310819253 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103335328401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_47 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (16491367861687 / 20000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206674638307 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨47, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (16491367861687 / 20000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206674638307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_48 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41211540152271 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206678693687 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨48, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41211540152271 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206678693687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_49 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (10298668074777 / 12500000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (34479417227 / 1562500000000 : ℝ))
      (E := (cell13084 ⟨49, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (10298668074777 / 12500000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (34479417227 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_50 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82355632160991 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (220668672107 / 10000000000000 : ℝ))
      (E := (cell13084 ⟨50, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82355632160991 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (220668672107 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_51 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82321942964541 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206690746393 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨51, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82321942964541 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206690746393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_52 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41144138490341 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (137918419769 / 6250000000000 : ℝ))
      (E := (cell13084 ⟨52, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41144138490341 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (137918419769 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_53 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (20563658545343 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (220669874557 / 10000000000000 : ℝ))
      (E := (cell13084 ⟨53, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (20563658545343 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (220669874557 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_54 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82221014538707 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206702771603 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨54, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82221014538707 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206702771603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_55 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (20546854506231 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441341358129 / 20000000000000 : ℝ))
      (E := (cell13084 ⟨55, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (20546854506231 / 25000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (441341358129 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_56 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82153844612397 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103355399367 / 50000000000000 : ℝ))
      (E := (cell13084 ⟨56, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82153844612397 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (1103355399367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_57 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82120294273637 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (22067147917 / 1000000000000 : ℝ))
      (E := (cell13084 ⟨57, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82120294273637 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (22067147917 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_58 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (41043383490647 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206718824373 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨58, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (41043383490647 / 50000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206718824373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13084_59 : CellCertificate 13084 (876265090488221 / 10000000000000000 : ℝ) (80266837430131 / 50000000000000000 : ℝ) (12961800121747 / 400000000000000 : ℝ)
    (cell13084 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · norm_num [cell13084]
  · have h := gap_lower (n := 13084) (a := (82053262708151 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206722833013 / 100000000000000 : ℝ))
      (E := (cell13084 ⟨59, by decide⟩).energy) (xi := (12961800121747 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13084 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13084]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13084])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13084) (a := (82053262708151 / 100000000000000 : ℝ)) (b := (157373787353 / 100000000000000 : ℝ)) (q := (2206722833013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13084])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13084]

theorem cert13085_40 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82693793085851 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206534221603 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨40, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82693793085851 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206534221603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_41 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (41329935097939 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206538188043 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨41, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (41329935097939 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206538188043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_42 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (16525194161359 / 20000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206542238837 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨42, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (16525194161359 / 20000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206542238837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_43 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (16518418977823 / 20000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206546255139 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨43, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (16518418977823 / 20000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206546255139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_44 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82558242413499 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (441310047091 / 20000000000000 : ℝ))
      (E := (cell13085 ⟨44, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82558242413499 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (441310047091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_45 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (20631103337689 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206554295877 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨45, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (20631103337689 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206554295877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_46 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82490607671839 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206558257847 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨46, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82490607671839 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206558257847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_47 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82456825347851 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (551640573999 / 25000000000000 : ℝ))
      (E := (cell13085 ⟨47, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82456825347851 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (551640573999 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_48 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (20605766587509 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (551641572543 / 25000000000000 : ℝ))
      (E := (cell13085 ⟨48, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (20605766587509 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (551641572543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_49 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (10298666331223 / 12500000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206570355797 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨49, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (10298666331223 / 12500000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206570355797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_50 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82355618218627 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103287186099 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨50, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82355618218627 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103287186099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_51 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (1029024112853 / 1250000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (441315667277 / 20000000000000 : ℝ))
      (E := (cell13085 ⟨51, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (1029024112853 / 1250000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (441315667277 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_52 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82288263050439 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206582363289 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨52, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82288263050439 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206582363289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_53 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82254620257183 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206586390551 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨53, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82254620257183 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206586390551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_54 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82221000620567 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206590414627 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨54, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82221000620567 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206590414627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_55 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (20546851028207 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103297215879 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨55, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (20546851028207 / 25000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103297215879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_56 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (82153830706339 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103299218991 / 50000000000000 : ℝ))
      (E := (cell13085 ⟨56, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (82153830706339 / 100000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (1103299218991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_57 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (41060140186807 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206602429129 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨57, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (41060140186807 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206602429129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_58 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (820867530873 / 1000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206606460029 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨58, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (820867530873 / 1000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206606460029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13085_59 : CellCertificate 13085 (876238706677659 / 10000000000000000 : ℝ) (1605214024182111 / 1000000000000000000 : ℝ) (324019668341273 / 10000000000000000 : ℝ)
    (cell13085 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · norm_num [cell13085]
  · have h := gap_lower (n := 13085) (a := (41026624410091 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206610466941 / 100000000000000 : ℝ))
      (E := (cell13085 ⟨59, by decide⟩).energy) (xi := (324019668341273 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13085 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13085]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13085])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13085) (a := (41026624410091 / 50000000000000 : ℝ)) (b := (157361621883 / 100000000000000 : ℝ)) (q := (2206610466941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13085])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13085]

theorem cert13086_40 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82693779084727 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206421833173 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨40, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82693779084727 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206421833173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_41 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (16531971240173 / 20000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103212927921 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨41, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (16531971240173 / 20000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103212927921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_42 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82625956817889 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206429904127 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨42, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82625956817889 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206429904127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_43 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82592080906311 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206433917967 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨43, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82592080906311 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206433917967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_44 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82558228436791 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206437895867 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨44, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82558228436791 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206437895867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_45 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (4126219969007 / 5000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103220976959 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨45, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (4126219969007 / 5000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103220976959 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_46 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (8249059370731 / 10000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (275805746561 / 12500000000000 : ℝ))
      (E := (cell13086 ⟨46, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (8249059370731 / 10000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (275805746561 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_47 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20614202847351 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (441289989887 / 20000000000000 : ℝ))
      (E := (cell13086 ⟨47, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20614202847351 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (441289989887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_48 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41211526198833 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (44129080007 / 2000000000000 : ℝ))
      (E := (cell13086 ⟨48, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41211526198833 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (44129080007 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_49 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41194658351743 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103229002409 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨49, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41194658351743 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103229002409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_50 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20588901069599 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103231009539 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨50, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20588901069599 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103231009539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_51 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82321915094071 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206466040213 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨51, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82321915094071 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206466040213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_52 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (10286031140291 / 12500000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551617516273 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨52, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (10286031140291 / 12500000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551617516273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_53 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20563651583781 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (275809253911 / 12500000000000 : ℝ))
      (E := (cell13086 ⟨53, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20563651583781 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (275809253911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_54 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (20555246676139 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206478053407 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨54, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (20555246676139 / 25000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206478053407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_55 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (4109369510143 / 5000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551620517157 / 25000000000000 : ℝ))
      (E := (cell13086 ⟨55, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (4109369510143 / 5000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (551620517157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_56 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (8215381680241 / 10000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206486072987 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨56, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (8215381680241 / 10000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206486072987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_57 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (41060133237859 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103245060749 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨57, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (41060133237859 / 50000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103245060749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_58 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82086739195433 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206494150649 / 100000000000000 : ℝ))
      (E := (cell13086 ⟨58, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82086739195433 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (2206494150649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13086_59 : CellCertificate 13086 (876212326727467 / 10000000000000000 : ℝ) (200636414815523 / 125000000000000000 : ℝ) (323994337629653 / 10000000000000000 : ℝ)
    (cell13086 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · norm_num [cell13086]
  · have h := gap_lower (n := 13086) (a := (82053234934339 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103249077929 / 50000000000000 : ℝ))
      (E := (cell13086 ⟨59, by decide⟩).energy) (xi := (323994337629653 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13086 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13086]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13086])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13086) (a := (82053234934339 / 100000000000000 : ℝ)) (b := (157349458301 / 100000000000000 : ℝ)) (q := (1103249077929 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13086])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13086]

theorem cert13087_40 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (16538753017149 / 20000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441261911611 / 20000000000000 : ℝ))
      (E := (cell13087 ⟨40, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (16538753017149 / 20000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441261911611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_41 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41329921103997 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103156789097 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨41, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41329921103997 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103156789097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_42 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82625942831123 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441263513033 / 20000000000000 : ℝ))
      (E := (cell13087 ⟨42, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82625942831123 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441263513033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_43 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41296033462823 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103160788271 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨43, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41296033462823 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103160788271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_44 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41279107231111 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441265122181 / 20000000000000 : ℝ))
      (E := (cell13087 ⟨44, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41279107231111 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441265122181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_45 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82524385411661 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206329607709 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨45, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82524385411661 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206329607709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_46 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41245289872459 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441266724791 / 20000000000000 : ℝ))
      (E := (cell13087 ⟨46, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41245289872459 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (441266724791 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_47 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (20614199358273 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103168828787 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨47, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (20614199358273 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103168828787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_48 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (8242303844743 / 10000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (220634164731 / 10000000000000 : ℝ))
      (E := (cell13087 ⟨48, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (8242303844743 / 10000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (220634164731 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_49 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82389302759321 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (275793206199 / 12500000000000 : ℝ))
      (E := (cell13087 ⟨49, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82389302759321 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (275793206199 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_50 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (41177795170149 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206349661713 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨50, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (41177795170149 / 50000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206349661713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_51 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (16464380232407 / 20000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103176840377 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨51, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (16464380232407 / 20000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103176840377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_52 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (20572058799087 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103178851793 / 50000000000000 : ℝ))
      (E := (cell13087 ⟨52, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (20572058799087 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (1103178851793 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_53 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (20563648103799 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206361726869 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨53, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (20563648103799 / 25000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206361726869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_54 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (3288838911627 / 4000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (137897859191 / 6250000000000 : ℝ))
      (E := (cell13087 ⟨54, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (3288838911627 / 4000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (137897859191 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_55 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82187376295021 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206369760391 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨55, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82187376295021 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206369760391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_56 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (641826585161 / 781250000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206373762911 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨56, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (641826585161 / 781250000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206373762911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_57 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82120252579949 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206377809627 / 100000000000000 : ℝ))
      (E := (cell13087 ⟨57, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82120252579949 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (2206377809627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_58 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82086725305691 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (220638183703 / 10000000000000 : ℝ))
      (E := (cell13087 ⟨58, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82086725305691 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (220638183703 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13087_59 : CellCertificate 13087 (219046487659189 / 2500000000000000 : ℝ) (320993726324907 / 200000000000000000 : ℝ) (323969010907817 / 10000000000000000 : ℝ)
    (cell13087 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · norm_num [cell13087]
  · have h := gap_lower (n := 13087) (a := (82053221050621 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (275798230067 / 12500000000000 : ℝ))
      (E := (cell13087 ⟨59, by decide⟩).energy) (xi := (323969010907817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13087 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13087]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13087])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13087) (a := (82053221050621 / 100000000000000 : ℝ)) (b := (78668648303 / 50000000000000 : ℝ)) (q := (275798230067 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13087])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13087]

theorem cert13088_40 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (16538750217781 / 20000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103098609949 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨40, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (16538750217781 / 20000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103098609949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_41 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82659828217263 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441240247497 / 20000000000000 : ℝ))
      (E := (cell13088 ⟨41, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82659828217263 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (441240247497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_42 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41312964423249 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103102640389 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨42, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41312964423249 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103102640389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_43 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (1032400661839 / 1250000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206209289719 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨43, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (1032400661839 / 1250000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206209289719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_44 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82558200489791 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206213321691 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨44, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82558200489791 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206213321691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_45 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (2063109286133 / 2500000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (44124346323 / 2000000000000 : ℝ))
      (E := (cell13088 ⟨45, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (2063109286133 / 2500000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (44124346323 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_46 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41245282892331 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (137888833131 / 6250000000000 : ℝ))
      (E := (cell13088 ⟨46, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41245282892331 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (137888833131 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_47 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (20614195869729 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103112680731 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨47, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (20614195869729 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103112680731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_48 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (8242302449933 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206229348991 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨48, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (8242302449933 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206229348991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_49 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82389288817291 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (275779168639 / 12500000000000 : ℝ))
      (E := (cell13088 ⟨49, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82389288817291 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (275779168639 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_50 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (20588894101083 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103118709069 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨50, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (20588894101083 / 25000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103118709069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_51 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (8232188723213 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206241435133 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨51, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (8232188723213 / 10000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206241435133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_52 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82288221272499 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (22062453969 / 1000000000000 : ℝ))
      (E := (cell13088 ⟨52, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82288221272499 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (22062453969 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_53 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41127289248699 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103124709103 / 50000000000000 : ℝ))
      (E := (cell13088 ⟨53, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41127289248699 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (1103124709103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_54 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41110479439461 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206253436463 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨54, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41110479439461 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206253436463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_55 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82187362389309 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206257447913 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨55, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82187362389309 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206257447913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_56 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (82153789000933 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (275782688469 / 12500000000000 : ℝ))
      (E := (cell13088 ⟨56, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (82153789000933 / 100000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (275782688469 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_57 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41060119343153 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (551566373379 / 25000000000000 : ℝ))
      (E := (cell13088 ⟨57, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41060119343153 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (551566373379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_58 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (3283468456723 / 4000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206269519171 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨58, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (3283468456723 / 4000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206269519171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13088_59 : CellCertificate 13088 (219039894601159 / 2500000000000000 : ℝ) (320969192695773 / 200000000000000000 : ℝ) (323943688174769 / 10000000000000000 : ℝ)
    (cell13088 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · norm_num [cell13088]
  · have h := gap_lower (n := 13088) (a := (41026603584513 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206273520977 / 100000000000000 : ℝ))
      (E := (cell13088 ⟨59, by decide⟩).energy) (xi := (323943688174769 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13088 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13088]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13088])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13088) (a := (41026603584513 / 50000000000000 : ℝ)) (b := (157325136799 / 100000000000000 : ℝ)) (q := (2206273520977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13088])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13088]

theorem cert13089_40 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41346868547103 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206084995057 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨40, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41346868547103 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206084995057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_41 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82659814228673 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103044505069 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨41, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82659814228673 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103044505069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_42 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20656478716003 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206092992141 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨42, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20656478716003 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206092992141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_43 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82592038970733 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103048499323 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨43, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82592038970733 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103048499323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_44 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41279093259749 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206101028227 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨44, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41279093259749 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206101028227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_45 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20631089370279 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103052510171 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨45, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20631089370279 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103052510171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_46 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41245275913271 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (220610903199 / 10000000000000 : ℝ))
      (E := (cell13089 ⟨46, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41245275913271 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (220610903199 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_47 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (131930831243 / 160000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (137882066319 / 6250000000000 : ℝ))
      (E := (cell13089 ⟨47, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (131930831243 / 160000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (137882066319 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_48 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82423010553363 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103058552699 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨48, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82423010553363 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103058552699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_49 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82389274877393 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (275765137923 / 12500000000000 : ℝ))
      (E := (cell13089 ⟨49, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82389274877393 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (275765137923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_50 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82355562470499 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (22061251113 / 1000000000000 : ℝ))
      (E := (cell13089 ⟨50, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82355562470499 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (22061251113 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_51 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20580468326089 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206129126227 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨51, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20580468326089 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206129126227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_52 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (4114410367539 / 5000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206133145037 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨52, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (4114410367539 / 5000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206133145037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_53 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82254564581729 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206137164391 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨53, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82254564581729 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206137164391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_54 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41110472484649 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206141180741 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨54, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41110472484649 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206141180741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_55 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (41093674242863 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206145190329 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨55, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (41093674242863 / 50000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206145190329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_56 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (16430755020677 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441229837839 / 20000000000000 : ℝ))
      (E := (cell13089 ⟨56, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (16430755020677 / 20000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (441229837839 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_57 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20530056198697 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (44123064647 / 2000000000000 : ℝ))
      (E := (cell13089 ⟨57, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20530056198697 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (44123064647 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_58 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (82086697532583 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103078628141 / 50000000000000 : ℝ))
      (E := (cell13089 ⟨58, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (82086697532583 / 100000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (1103078628141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13089_59 : CellCertificate 13089 (876133210030221 / 10000000000000000 : ℝ) (1604723314082873 / 1000000000000000000 : ℝ) (323918369429511 / 10000000000000000 : ℝ)
    (cell13089 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · norm_num [cell13089]
  · have h := gap_lower (n := 13089) (a := (20513298322389 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206161256409 / 100000000000000 : ℝ))
      (E := (cell13089 ⟨59, by decide⟩).energy) (xi := (323918369429511 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13089 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13089]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13089])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13089) (a := (20513298322389 / 25000000000000 : ℝ)) (b := (78656489439 / 50000000000000 : ℝ)) (q := (2206161256409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13089])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13089]

theorem cert13090_40 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (5168357693853 / 6250000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102986353589 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨40, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (5168357693853 / 6250000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1102986353589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_41 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82659800242223 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551494179933 / 25000000000000 : ℝ))
      (E := (cell13090 ⟨41, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82659800242223 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551494179933 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_42 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (16525180176733 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551495189521 / 25000000000000 : ℝ))
      (E := (cell13090 ⟨42, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (16525180176733 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551495189521 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_43 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (20648006249121 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205984762177 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨43, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (20648006249121 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205984762177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_44 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41279086275671 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205988789391 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨44, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41279086275671 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205988789391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_45 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (10315542939881 / 12500000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205992779187 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨45, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (10315542939881 / 12500000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205992779187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_46 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82490537870557 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205996788561 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨46, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82490537870557 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2205996788561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_47 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82456755576969 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2206000815447 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨47, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82456755576969 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2206000815447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_48 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82422996609529 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (55150121439 / 2500000000000 : ℝ))
      (E := (cell13090 ⟨48, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82422996609529 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (55150121439 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_49 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (20597315234907 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2206008853409 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨49, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (20597315234907 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2206008853409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_50 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41177774269399 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441202571847 / 20000000000000 : ℝ))
      (E := (cell13090 ⟨50, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41177774269399 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441202571847 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_51 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82321859378713 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2206016872119 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨51, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82321859378713 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2206016872119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_52 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82288193431191 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551505222233 / 25000000000000 : ℝ))
      (E := (cell13090 ⟨52, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82288193431191 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (551505222233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_53 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (20563637667047 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1103012453167 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨53, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (20563637667047 / 25000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1103012453167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_54 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (41110465530901 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1103014460389 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨54, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (41110465530901 / 50000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1103014460389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_55 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82187334584269 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1103016464253 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨55, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82187334584269 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1103016464253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_56 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82153761207963 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2206036984717 / 100000000000000 : ℝ))
      (E := (cell13090 ⟨56, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82153761207963 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (2206036984717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_57 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (16424042181079 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441208193389 / 20000000000000 : ℝ))
      (E := (cell13090 ⟨57, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (16424042181079 / 20000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441208193389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_58 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (1282604432019 / 1562500000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1103022494577 / 50000000000000 : ℝ))
      (E := (cell13090 ⟨58, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (1282604432019 / 1562500000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (1103022494577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13090_59 : CellCertificate 13090 (438053422756311 / 5000000000000000 : ℝ) (80230034171613 / 50000000000000000 : ℝ) (40486631833881 / 1250000000000000 : ℝ)
    (cell13090 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · norm_num [cell13090]
  · have h := gap_lower (n := 13090) (a := (82053179412209 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441209797521 / 20000000000000 : ℝ))
      (E := (cell13090 ⟨59, by decide⟩).energy) (xi := (40486631833881 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13090 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13090]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13090])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13090) (a := (82053179412209 / 100000000000000 : ℝ)) (b := (39325205711 / 25000000000000 : ℝ)) (q := (441209797521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13090])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13090]

theorem cert13091_40 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (8269370911123 / 10000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205860473833 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨40, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (8269370911123 / 10000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205860473833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_41 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82659786257913 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102932241941 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨41, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82659786257913 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102932241941 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_42 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (5164117931591 / 6250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205868519779 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨42, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (5164117931591 / 6250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205868519779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_43 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20648002756093 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (110293626073 / 5000000000000 : ℝ))
      (E := (cell13091 ⟨43, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20648002756093 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (110293626073 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_44 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82558158585323 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205876546309 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨44, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82558158585323 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205876546309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_45 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20631082389779 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441176106757 / 20000000000000 : ℝ))
      (E := (cell13091 ⟨45, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20631082389779 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441176106757 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_46 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82490523916707 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551471149953 / 25000000000000 : ℝ))
      (E := (cell13091 ⟨46, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82490523916707 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551471149953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_47 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20614185407299 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441177713109 / 20000000000000 : ℝ))
      (E := (cell13091 ⟨47, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20614185407299 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (441177713109 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_48 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82422982667829 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205892605477 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨48, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82422982667829 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205892605477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_49 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (16477849400799 / 20000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (275737074899 / 12500000000000 : ℝ))
      (E := (cell13091 ⟨49, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (16477849400799 / 20000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (275737074899 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_50 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82355534609227 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551475165487 / 25000000000000 : ℝ))
      (E := (cell13091 ⟨50, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82355534609227 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551475165487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_51 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (102902306819 / 125000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205904672813 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨51, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (102902306819 / 125000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205904672813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_52 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82288179513731 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551477171913 / 25000000000000 : ℝ))
      (E := (cell13091 ⟨52, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82288179513731 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551477171913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_53 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (10281817094597 / 12500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205912703127 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨53, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (10281817094597 / 12500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205912703127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_54 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41110458578217 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (275739589461 / 12500000000000 : ℝ))
      (E := (cell13091 ⟨54, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41110458578217 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (275739589461 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_55 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (82187320684939 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205920721581 / 100000000000000 : ℝ))
      (E := (cell13091 ⟨55, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (82187320684939 / 100000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (2205920721581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_56 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (41076873657333 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551481179211 / 25000000000000 : ℝ))
      (E := (cell13091 ⟨56, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (41076873657333 / 50000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (551481179211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_57 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (5132512313633 / 6250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102964378243 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨57, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (5132512313633 / 6250000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102964378243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_58 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (20521667441993 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102966388499 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨58, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (20521667441993 / 25000000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102966388499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13091_59 : CellCertificate 13091 (876080484850951 / 10000000000000000 : ℝ) (160447807152273 / 100000000000000000 : ℝ) (20241733993649 / 625000000000000 : ℝ)
    (cell13091 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · norm_num [cell13091]
  · have h := gap_lower (n := 13091) (a := (10256645692123 / 12500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102968386899 / 50000000000000 : ℝ))
      (E := (cell13091 ⟨59, by decide⟩).energy) (xi := (20241733993649 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13091 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13091]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13091])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13091) (a := (10256645692123 / 12500000000000 : ℝ)) (b := (31457733739 / 20000000000000 : ℝ)) (q := (1102968386899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13091])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13091]

theorem cert13092_40 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82693695122953 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205748295021 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨40, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82693695122953 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205748295021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_41 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41329886137871 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205752302591 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨41, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41329886137871 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205752302591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_42 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41312936464693 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205756277223 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨42, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41312936464693 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205756277223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_43 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41295998527199 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551440083837 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨43, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41295998527199 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551440083837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_44 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (128997100971 / 156250000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (68930136183 / 3125000000000 : ℝ))
      (E := (cell13092 ⟨44, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (128997100971 / 156250000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (68930136183 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_45 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82524315601319 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102884171519 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨45, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82524315601319 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102884171519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_46 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82490509964991 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205772347891 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨46, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82490509964991 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205772347891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_47 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (20614181920889 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551444092587 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨47, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (20614181920889 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551444092587 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_48 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82422968728261 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205780408123 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨48, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82422968728261 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205780408123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_49 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82389233070493 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205784399727 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨49, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82389233070493 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205784399727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_50 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82355520681787 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (11028942007 / 500000000000 : ℝ))
      (E := (cell13092 ⟨50, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82355520681787 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (11028942007 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_51 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (82321831533817 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102896205111 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨51, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (82321831533817 / 100000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102896205111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_52 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (51430103499 / 62500000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205796482131 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨52, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (51430103499 / 62500000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205796482131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_53 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (20563630711873 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205800495679 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨53, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (20563630711873 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205800495679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_54 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (10277612906649 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (55145112659 / 2500000000000 : ℝ))
      (E := (cell13092 ⟨54, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (10277612906649 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (55145112659 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_55 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41093653393867 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205808510419 / 100000000000000 : ℝ))
      (E := (cell13092 ⟨55, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41093653393867 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (2205808510419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_56 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41076866711747 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551453125973 / 25000000000000 : ℝ))
      (E := (cell13092 ⟨56, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41076866711747 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (551453125973 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_57 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (10265022891623 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (68931766931 / 3125000000000 : ℝ))
      (E := (cell13092 ⟨57, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (10265022891623 / 12500000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (68931766931 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_58 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (20521663972213 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102910280303 / 50000000000000 : ℝ))
      (E := (cell13092 ⟨58, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (20521663972213 / 25000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (1102910280303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13092_59 : CellCertificate 13092 (438027064022161 / 5000000000000000 : ℝ) (1604355478349987 / 1000000000000000000 : ℝ) (80960609277631 / 2500000000000000 : ℝ)
    (cell13092 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · norm_num [cell13092]
  · have h := gap_lower (n := 13092) (a := (41026575831941 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441164911151 / 20000000000000 : ℝ))
      (E := (cell13092 ⟨59, by decide⟩).energy) (xi := (80960609277631 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13092 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13092]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13092])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13092) (a := (41026575831941 / 50000000000000 : ℝ)) (b := (9829782277 / 6250000000000 : ℝ)) (q := (441164911151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13092])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13092]

theorem cert13093_40 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (16538736227363 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (55140902799 / 2500000000000 : ℝ))
      (E := (cell13093 ⟨40, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (16538736227363 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (55140902799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_41 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82659758295709 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551410029263 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨41, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82659758295709 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551410029263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_42 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82625858955453 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551411022313 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨42, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82625858955453 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551411022313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_43 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82591983086561 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205648144991 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨43, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82591983086561 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205648144991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_44 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (20639532664923 / 25000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (55141304129 / 2500000000000 : ℝ))
      (E := (cell13093 ⟨44, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (20639532664923 / 25000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (55141304129 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_45 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82524301645657 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205656148047 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨45, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82524301645657 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205656148047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_46 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82490496015409 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205660150653 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨46, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82490496015409 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205660150653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_47 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (1649134274801 / 2000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205664170907 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨47, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (1649134274801 / 2000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205664170907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_48 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (3296918191633 / 4000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205668206527 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨48, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (3296918191633 / 4000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205668206527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_49 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82389219139123 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205672196021 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨49, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82389219139123 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205672196021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_50 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82355506756477 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205676254649 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨50, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82355506756477 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205676254649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_51 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82321817614563 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102840130739 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨51, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82321817614563 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102840130739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_52 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82288151685197 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551421068093 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨52, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82288151685197 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551421068093 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_53 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (5140906808771 / 6250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102844141997 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨53, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (5140906808771 / 6250000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102844141997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_54 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (20555222338019 / 25000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551423073199 / 25000000000000 : ℝ))
      (E := (cell13093 ⟨54, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (20555222338019 / 25000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (551423073199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_55 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (16437458578531 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205696295021 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨55, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (16437458578531 / 20000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205696295021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_56 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (82153719534447 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102850172933 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨56, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (82153719534447 / 100000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102850172933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_57 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (20530042312491 / 25000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (137856520179 / 6250000000000 : ℝ))
      (E := (cell13093 ⟨57, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (20530042312491 / 25000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (137856520179 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_58 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (41043321005927 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102854169991 / 50000000000000 : ℝ))
      (E := (cell13093 ⟨58, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (41043321005927 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (1102854169991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13093_59 : CellCertificate 13093 (109503471886481 / 1250000000000000 : ℝ) (200529112988717 / 125000000000000000 : ℝ) (40477141788309 / 1250000000000000 : ℝ)
    (cell13093 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · norm_num [cell13093]
  · have h := gap_lower (n := 13093) (a := (41026568896451 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205712392711 / 100000000000000 : ℝ))
      (E := (cell13093 ⟨59, by decide⟩).energy) (xi := (40477141788309 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13093 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13093]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13093])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13093) (a := (41026568896451 / 50000000000000 : ℝ)) (b := (157264366053 / 100000000000000 : ℝ)) (q := (2205712392711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13093])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13093]

theorem cert13094_40 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (5168354197051 / 6250000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205523924651 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨40, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (5168354197051 / 6250000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205523924651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_41 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41329872158907 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441105585453 / 20000000000000 : ℝ))
      (E := (cell13094 ⟨41, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41329872158907 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441105585453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_42 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82625844983657 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441106391173 / 20000000000000 : ℝ))
      (E := (cell13094 ⟨42, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82625844983657 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441106391173 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_43 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82591969120859 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551383987597 / 25000000000000 : ℝ))
      (E := (cell13094 ⟨43, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82591969120859 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551383987597 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_44 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (1031976458751 / 1250000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205539968217 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨44, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (1031976458751 / 1250000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205539968217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_45 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82524287692129 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205544007713 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨45, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82524287692129 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205544007713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_46 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82490482067961 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441109601619 / 20000000000000 : ℝ))
      (E := (cell13094 ⟨46, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82490482067961 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441109601619 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_47 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (20614174949669 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551388006543 / 25000000000000 : ℝ))
      (E := (cell13094 ⟨47, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (20614174949669 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551388006543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_48 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (515143380347 / 625000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205556059661 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨48, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (515143380347 / 625000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205556059661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_49 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82389205209883 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (220556004707 / 10000000000000 : ℝ))
      (E := (cell13094 ⟨49, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82389205209883 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (220556004707 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_50 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82355492833297 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205564044639 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨50, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82355492833297 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205564044639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_51 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41160901848719 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205568108493 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨51, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41160901848719 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205568108493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_52 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41144068887061 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (6892412867 / 312500000000 : ℝ))
      (E := (cell13094 ⟨52, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41144068887061 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (6892412867 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_53 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41127247517653 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205576127161 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨53, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41127247517653 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205576127161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_54 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82220875453087 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205580134107 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨54, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82220875453087 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205580134107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_55 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41093639499851 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205584134523 / 100000000000000 : ℝ))
      (E := (cell13094 ⟨55, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41093639499851 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (2205584134523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_56 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (20538426411881 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441117636721 / 20000000000000 : ℝ))
      (E := (cell13094 ⟨56, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (20538426411881 / 25000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (441117636721 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_57 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82120155369067 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551398039721 / 25000000000000 : ℝ))
      (E := (cell13094 ⟨57, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82120155369067 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551398039721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_58 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (41043314068489 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551399043583 / 25000000000000 : ℝ))
      (E := (cell13094 ⟨58, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (41043314068489 / 50000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (551399043583 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13094_59 : CellCertificate 13094 (876001425992641 / 10000000000000000 : ℝ) (401027587049421 / 250000000000000000 : ℝ) (64758367097047 / 2000000000000000 : ℝ)
    (cell13094 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · norm_num [cell13094]
  · have h := gap_lower (n := 13094) (a := (82053123924043 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102800112717 / 50000000000000 : ℝ))
      (E := (cell13094 ⟨59, by decide⟩).energy) (xi := (64758367097047 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13094 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13094]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13094])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13094) (a := (82053123924043 / 100000000000000 : ℝ)) (b := (157252217559 / 100000000000000 : ℝ)) (q := (1102800112717 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13094])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13094]

theorem cert13095_40 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16538730634191 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205411791879 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨40, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16538730634191 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205411791879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_41 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (10332466292757 / 12500000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205415792041 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨41, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (10332466292757 / 12500000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205415792041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_42 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41312915506999 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205419818233 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨42, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41312915506999 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205419818233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_43 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82591955157293 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (441084762079 / 20000000000000 : ℝ))
      (E := (cell13095 ⟨43, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82591955157293 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (441084762079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_44 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82558102742603 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205427825909 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨44, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82558102742603 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205427825909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_45 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16504854748147 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (68919745723 / 3125000000000 : ℝ))
      (E := (cell13095 ⟨45, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16504854748147 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (68919745723 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_46 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16498093624529 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (137839741331 / 6250000000000 : ℝ))
      (E := (cell13095 ⟨46, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16498093624529 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (137839741331 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_47 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41228342929717 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551359969299 / 25000000000000 : ℝ))
      (E := (cell13095 ⟨47, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41228342929717 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (551359969299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_48 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82422926922347 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102721954277 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨48, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82422926922347 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102721954277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_49 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82389191282773 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205447893879 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨49, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82389191282773 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205447893879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_50 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41177739456123 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205451948429 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨50, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41177739456123 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205451948429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_51 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82321789782441 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275681993909 / 12500000000000 : ℝ))
      (E := (cell13095 ⟨51, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82321789782441 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275681993909 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_52 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41144061932587 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (4307538981 / 195312500000 : ℝ))
      (E := (cell13095 ⟨52, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41144061932587 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (4307538981 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_53 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (41127240566201 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205463966093 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨53, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (41127240566201 / 50000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205463966093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_54 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82220861556223 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (137841748199 / 6250000000000 : ℝ))
      (E := (cell13095 ⟨54, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82220861556223 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (137841748199 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_55 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (10273408138609 / 12500000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (8615125113 / 390625000000 : ℝ))
      (E := (cell13095 ⟨55, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (10273408138609 / 12500000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (8615125113 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_56 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (3286147670509 / 4000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205476017109 / 100000000000000 : ℝ))
      (E := (cell13095 ⟨56, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (3286147670509 / 4000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (2205476017109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_57 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (82120141490293 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (34460625779 / 1562500000000 : ℝ))
      (E := (cell13095 ⟨57, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (82120141490293 / 100000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (34460625779 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_58 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (2565206695757 / 3125000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275685507957 / 12500000000000 : ℝ))
      (E := (cell13095 ⟨58, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (2565206695757 / 3125000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (275685507957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13095_59 : CellCertificate 13095 (175195016149163 / 2000000000000000 : ℝ) (1603987811209539 / 1000000000000000000 : ℝ) (323766540645817 / 10000000000000000 : ℝ)
    (cell13095 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · norm_num [cell13095]
  · have h := gap_lower (n := 13095) (a := (16410622011461 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102744026963 / 50000000000000 : ℝ))
      (E := (cell13095 ⟨59, by decide⟩).energy) (xi := (323766540645817 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13095 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13095]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13095])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13095) (a := (16410622011461 / 20000000000000 : ℝ)) (b := (157240070949 / 100000000000000 : ℝ)) (q := (1102744026963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13095])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13095]

theorem cert13096_40 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (1292088112363 / 1562500000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205299654861 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨40, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (1292088112363 / 1562500000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205299654861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_41 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (20664929092109 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (220530365257 / 10000000000000 : ℝ))
      (E := (cell13096 ⟨41, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (20664929092109 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (220530365257 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_42 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (3305032681859 / 4000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205307676357 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨42, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (3305032681859 / 4000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205307676357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_43 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82591941195863 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102655833079 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨43, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82591941195863 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102655833079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_44 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82558088787259 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205315679359 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨44, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82558088787259 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205315679359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_45 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41262129895737 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205319714319 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨45, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41262129895737 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205319714319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_46 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (41245227089731 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (137832731891 / 6250000000000 : ℝ))
      (E := (cell13096 ⟨46, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (41245227089731 / 50000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (137832731891 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_47 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82456671922323 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205327723981 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨47, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82456671922323 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205327723981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_48 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (10302864123913 / 12500000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205331753209 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨48, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (10302864123913 / 12500000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205331753209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_49 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82389177357793 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102667897723 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨49, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82389177357793 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102667897723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_50 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (20588866248331 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102669894481 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨50, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (20588866248331 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102669894481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_51 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (20580443967393 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205343789813 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨51, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (20580443967393 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205343789813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_52 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82288109958353 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (441069570787 / 20000000000000 : ℝ))
      (E := (cell13096 ⟨52, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82288109958353 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (441069570787 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_53 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (658035737853 / 800000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102675929939 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨53, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (658035737853 / 800000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102675929939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_54 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (20555211915371 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (110267793157 / 5000000000000 : ℝ))
      (E := (cell13096 ⟨54, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (20555211915371 / 25000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (110267793157 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_55 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82187251220167 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102679929981 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨55, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82187251220167 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102679929981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_56 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82153677880049 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102681952771 / 50000000000000 : ℝ))
      (E := (cell13096 ⟨56, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82153677880049 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (1102681952771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_57 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82120127613641 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (551341984149 / 25000000000000 : ℝ))
      (E := (cell13096 ⟨57, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82120127613641 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (551341984149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_58 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (10260825049199 / 12500000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205371948749 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨58, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (10260825049199 / 12500000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205371948749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13096_59 : CellCertificate 13096 (175189747870097 / 2000000000000000 : ℝ) (1603865292941011 / 1000000000000000000 : ℝ) (12949649991489 / 400000000000000 : ℝ)
    (cell13096 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · norm_num [cell13096]
  · have h := gap_lower (n := 13096) (a := (82053096192687 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205375937419 / 100000000000000 : ℝ))
      (E := (cell13096 ⟨59, by decide⟩).energy) (xi := (12949649991489 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13096 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13096]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13096])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13096) (a := (82053096192687 / 100000000000000 : ℝ)) (b := (78613963111 / 50000000000000 : ℝ)) (q := (2205375937419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13096])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13096]

theorem cert13097_40 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82693625213647 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205187513597 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨40, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82693625213647 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205187513597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_41 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (10332462799619 / 12500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205191567663 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨41, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (10332462799619 / 12500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205191567663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_42 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (645514086571 / 781250000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205195589067 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨42, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (645514086571 / 781250000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205195589067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_43 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82591927236567 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205199576533 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨43, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82591927236567 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205199576533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_44 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (1651161496681 / 2000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (551300896861 / 25000000000000 : ℝ))
      (E := (cell13097 ⟨44, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (1651161496681 / 2000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (551300896861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_45 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41262122922173 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205207620161 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨45, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41262122922173 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205207620161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_46 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (8249044023841 / 10000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205211613901 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨46, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (8249044023841 / 10000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205211613901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_47 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82456657987343 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102607812737 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨47, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82456657987343 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102607812737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_48 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82422899062391 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205219652597 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨48, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82422899062391 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205219652597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_49 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41194581717471 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102611846387 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨49, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41194581717471 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102611846387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_50 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (8235545107653 / 10000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102613842139 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨50, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (8235545107653 / 10000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102613842139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_51 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (8232176195883 / 10000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205231683161 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨51, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (8232176195883 / 10000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205231683161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_52 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41144048026829 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102617872681 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨52, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41144048026829 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102617872681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_53 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (20563613333243 / 25000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (220523974943 / 10000000000000 : ℝ))
      (E := (cell13097 ⟨53, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (20563613333243 / 25000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (220523974943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_54 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82220833768869 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102621875431 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨54, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82220833768869 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102621875431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_55 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (41093618666793 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (22052477459 / 1000000000000 : ℝ))
      (E := (cell13097 ⟨55, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (41093618666793 / 50000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (22052477459 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_56 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (16430732799899 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205251789743 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨56, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (16430732799899 / 20000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205251789743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_57 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82120113739111 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (441051163821 / 20000000000000 : ℝ))
      (E := (cell13097 ⟨57, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82120113739111 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (441051163821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_58 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (2052164663127 / 2500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205259829613 / 100000000000000 : ℝ))
      (E := (cell13097 ⟨58, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (2052164663127 / 2500000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (2205259829613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13097_59 : CellCertificate 13097 (218980600451441 / 2500000000000000 : ℝ) (1603742793387809 / 1000000000000000000 : ℝ) (161857981454233 / 5000000000000000 : ℝ)
    (cell13097 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · norm_num [cell13097]
  · have h := gap_lower (n := 13097) (a := (82053082330189 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102631908341 / 50000000000000 : ℝ))
      (E := (cell13097 ⟨59, by decide⟩).energy) (xi := (161857981454233 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13097 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13097]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13097])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13097) (a := (82053082330189 / 100000000000000 : ℝ)) (b := (157215783379 / 100000000000000 : ℝ)) (q := (1102631908341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13097])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13097]

theorem cert13098_40 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82693611238199 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102537713437 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨40, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82693611238199 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102537713437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_41 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (16531937685521 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (137817467407 / 6250000000000 : ℝ))
      (E := (cell13098 ⟨41, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (16531937685521 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (137817467407 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_42 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (20656447279459 / 25000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (34454429649 / 1562500000000 : ℝ))
      (E := (cell13098 ⟨42, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (20656447279459 / 25000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (34454429649 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_43 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (16518382655881 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205087482667 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨43, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (16518382655881 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205087482667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_44 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41279030441487 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205091491289 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨44, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41279030441487 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205091491289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_45 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (1650484637987 / 2000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551273880441 / 25000000000000 : ℝ))
      (E := (cell13098 ⟨45, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (1650484637987 / 2000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551273880441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_46 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (8249042629949 / 10000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205099572233 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨46, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (8249042629949 / 10000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205099572233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_47 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41228322027247 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205103581679 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨47, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41228322027247 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205103581679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_48 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82422885135607 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551276886937 / 25000000000000 : ℝ))
      (E := (cell13098 ⟨48, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82422885135607 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551276886937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_49 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82389149514219 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205111585867 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨49, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82389149514219 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205111585867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_50 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (10294429645233 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205115634377 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨50, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (10294429645233 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205115634377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_51 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (16464349610043 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205119631317 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨51, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (16464349610043 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205119631317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_52 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (8228808215109 / 10000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102561816277 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨52, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (8228808215109 / 10000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102561816277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_53 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (16450887887289 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205127634749 / 100000000000000 : ℝ))
      (E := (cell13098 ⟨53, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (16450887887289 / 20000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (2205127634749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_54 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82220819878379 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441026338693 / 20000000000000 : ℝ))
      (E := (cell13098 ⟨54, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82220819878379 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441026338693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_55 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82187223449127 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (275641960843 / 12500000000000 : ℝ))
      (E := (cell13098 ⟨55, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82187223449127 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (275641960843 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_56 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (10269206265133 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102569864437 / 50000000000000 : ℝ))
      (E := (cell13098 ⟨56, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (10269206265133 / 12500000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (1102569864437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_57 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (41060049933351 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441028739477 / 20000000000000 : ℝ))
      (E := (cell13098 ⟨57, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (41060049933351 / 50000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441028739477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_58 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82086572658689 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441029553091 / 20000000000000 : ℝ))
      (E := (cell13098 ⟨58, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82086572658689 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (441029553091 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13098_59 : CellCertificate 13098 (437948034055383 / 5000000000000000 : ℝ) (1603620312545647 / 1000000000000000000 : ℝ) (323690680008547 / 10000000000000000 : ℝ)
    (cell13098 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · norm_num [cell13098]
  · have h := gap_lower (n := 13098) (a := (82053068469811 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551287937737 / 25000000000000 : ℝ))
      (E := (cell13098 ⟨59, by decide⟩).energy) (xi := (323690680008547 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13098 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13098]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13098])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13098) (a := (82053068469811 / 100000000000000 : ℝ)) (b := (78601821209 / 50000000000000 : ℝ)) (q := (551287937737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13098])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13098]

theorem cert13099_40 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82693597264887 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204963394693 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨40, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82693597264887 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204963394693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_41 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (10332459307549 / 12500000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204967385121 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨41, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (10332459307549 / 12500000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204967385121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_42 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41312887578359 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551242850441 / 25000000000000 : ℝ))
      (E := (cell13099 ⟨42, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41312887578359 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (551242850441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_43 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82591899324377 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (275621930427 / 12500000000000 : ℝ))
      (E := (cell13099 ⟨43, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82591899324377 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (275621930427 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_44 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (8255804693403 / 10000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102489724887 / 50000000000000 : ℝ))
      (E := (cell13099 ⟨44, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (8255804693403 / 10000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (1102489724887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_45 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82524217956487 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204983478029 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨45, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82524217956487 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204983478029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_46 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82490412362701 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204987467401 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨46, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82490412362701 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204987467401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_47 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (3298265204951 / 4000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204991474697 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨47, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (3298265204951 / 4000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2204991474697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_48 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82422871210953 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (440999099527 / 20000000000000 : ℝ))
      (E := (cell13099 ⟨48, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82422871210953 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (440999099527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_49 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (131822616953 / 160000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (55124988343 / 2500000000000 : ℝ))
      (E := (cell13099 ⟨49, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (131822616953 / 160000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (55124988343 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_50 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (20588855812331 / 25000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205003521223 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨50, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (20588855812331 / 25000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205003521223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_51 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41160867071863 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205007575241 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨51, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41160867071863 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205007575241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_52 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41144034125323 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205011574581 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨52, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41144034125323 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205011574581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_53 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41127212771021 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (88200622997 / 4000000000000 : ℝ))
      (E := (cell13099 ⟨53, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41127212771021 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (88200622997 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_54 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (20555201497503 / 25000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205019631837 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨54, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (20555201497503 / 25000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205019631837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_55 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82187209566791 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205023623359 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨55, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82187209566791 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205023623359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_56 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (41076818122377 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (68907114493 / 3125000000000 : ℝ))
      (E := (cell13099 ⟨56, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (41076818122377 / 50000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (68907114493 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_57 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82120085996413 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (441006337961 / 20000000000000 : ℝ))
      (E := (cell13099 ⟨57, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82120085996413 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (441006337961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_58 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82086558794417 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (220503569707 / 10000000000000 : ℝ))
      (E := (cell13099 ⟨58, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82086558794417 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (220503569707 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

theorem cert13099_59 : CellCertificate 13099 (875869738264607 / 10000000000000000 : ℝ) (1603497850410237 / 1000000000000000000 : ℝ) (161832700543237 / 5000000000000000 : ℝ)
    (cell13099 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · norm_num [cell13099]
  · have h := gap_lower (n := 13099) (a := (82053054611551 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205039680989 / 100000000000000 : ℝ))
      (E := (cell13099 ⟨59, by decide⟩).energy) (xi := (161832700543237 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13099 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13099]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13099])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13099) (a := (82053054611551 / 100000000000000 : ℝ)) (b := (157191503339 / 100000000000000 : ℝ)) (q := (2205039680989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13099])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13099]

end BstLean.Part268
