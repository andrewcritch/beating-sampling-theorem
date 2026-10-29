import BstLean.Part268CellShard23Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12925_40 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82695516135169 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (27810011507 / 1250000000000 : ℝ))
      (E := (cell12925 ⟨40, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82695516135169 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (27810011507 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_41 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82661579015593 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224804946323 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨41, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82661579015593 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224804946323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_42 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82627665416111 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112404480513 / 50000000000000 : ℝ))
      (E := (cell12925 ⟨42, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82627665416111 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112404480513 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_43 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82593775307197 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224812963499 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨43, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82593775307197 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224812963499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_44 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41279954329739 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224816952351 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨44, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41279954329739 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224816952351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_45 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82526065443727 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224820984861 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨45, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82526065443727 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224820984861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_46 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (5155765351929 / 6250000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (222482500037 / 10000000000000 : ℝ))
      (E := (cell12925 ⟨46, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (5155765351929 / 6250000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (222482500037 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_47 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (16491689838391 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112414498421 / 50000000000000 : ℝ))
      (E := (cell12925 ⟨47, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (16491689838391 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112414498421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_48 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82424676098211 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (278104128873 / 12500000000000 : ℝ))
      (E := (cell12925 ⟨48, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82424676098211 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (278104128873 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_49 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82390926320987 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224837041423 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨49, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82390926320987 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224837041423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_50 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82357199831781 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224841025487 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨50, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82357199831781 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224841025487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_51 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (16464699320447 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112422519657 / 50000000000000 : ℝ))
      (E := (cell12925 ⟨51, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (16464699320447 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112422519657 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_52 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20572454151033 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224849020829 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨52, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20572454151033 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224849020829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_53 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (16451231961879 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (11124265129 / 500000000000 : ℝ))
      (E := (cell12925 ⟨53, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (16451231961879 / 20000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (11124265129 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_54 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (10277815773761 / 12500000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (111242852539 / 5000000000000 : ℝ))
      (E := (cell12925 ⟨54, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (10277815773761 / 12500000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (111242852539 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_55 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41094457859207 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224861092117 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨55, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41094457859207 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224861092117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_56 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20538832091679 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112432543403 / 50000000000000 : ℝ))
      (E := (cell12925 ⟨56, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20538832091679 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (1112432543403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_57 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (82121764107471 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556217272469 / 25000000000000 : ℝ))
      (E := (cell12925 ⟨57, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (82121764107471 / 100000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (556217272469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_58 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (41044111456649 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224873097053 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨58, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (41044111456649 / 50000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224873097053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12925_59 : CellCertificate 12925 (176101966931383 / 2000000000000000 : ℝ) (812545782661787 / 500000000000000000 : ℝ) (328124675622449 / 10000000000000000 : ℝ)
    (cell12925 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · norm_num [cell12925]
  · have h := gap_lower (n := 12925) (a := (20513676189237 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224877103857 / 100000000000000 : ℝ))
      (E := (cell12925 ⟨59, by decide⟩).energy) (xi := (328124675622449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12925 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12925]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12925])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12925) (a := (20513676189237 / 25000000000000 : ℝ)) (b := (39833106597 / 25000000000000 : ℝ)) (q := (2224877103857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12925])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12925]

theorem cert12926_40 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (8269551365513 / 10000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112342438569 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨40, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (8269551365513 / 10000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112342438569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_41 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41330788415071 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224688850007 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨41, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41330788415071 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224688850007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_42 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82627663524841 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112346435633 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨42, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82627663524841 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112346435633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_43 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (10324221713713 / 12500000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (139043555061 / 6250000000000 : ℝ))
      (E := (cell12926 ⟨43, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (10324221713713 / 12500000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (139043555061 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_44 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82559907355357 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444940175549 / 20000000000000 : ℝ))
      (E := (cell12926 ⟨44, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82559907355357 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444940175549 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_45 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (3301042577303 / 4000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556176229713 / 25000000000000 : ℝ))
      (E := (cell12926 ⟨45, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (3301042577303 / 4000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556176229713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_46 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41246122456139 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (278088610591 / 12500000000000 : ℝ))
      (E := (cell12926 ⟨46, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41246122456139 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (278088610591 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_47 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (20614612191383 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (139044559379 / 6250000000000 : ℝ))
      (E := (cell12926 ⟨47, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (20614612191383 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (139044559379 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_48 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82424675963551 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (55617923397 / 2500000000000 : ℝ))
      (E := (cell12926 ⟨48, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82424675963551 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (55617923397 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_49 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (10298865809711 / 12500000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112360478803 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨49, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (10298865809711 / 12500000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112360478803 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_50 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (20589300069861 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (222472495363 / 10000000000000 : ℝ))
      (E := (cell12926 ⟨50, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (20589300069861 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (222472495363 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_51 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82323497340461 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112364490047 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨51, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82323497340461 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112364490047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_52 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82289817632521 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112366487461 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨52, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82289817632521 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112366487461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_53 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (1645123222551 / 2000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112368496939 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨53, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (1645123222551 / 2000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112368496939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_54 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (20555631949403 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224740974421 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨54, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (20555631949403 / 25000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224740974421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_55 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82188917614911 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112372485973 / 50000000000000 : ℝ))
      (E := (cell12926 ⟨55, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82188917614911 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (1112372485973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_56 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82155330551789 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224748982593 / 100000000000000 : ℝ))
      (E := (cell12926 ⟨56, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82155330551789 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (2224748982593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_57 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41060883290363 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556188250573 / 25000000000000 : ℝ))
      (E := (cell12926 ⟨57, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41060883290363 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (556188250573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_58 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (82088225674339 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (222475702677 / 10000000000000 : ℝ))
      (E := (cell12926 ⟨58, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (82088225674339 / 100000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (222475702677 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12926_59 : CellCertificate 12926 (440241412775827 / 5000000000000000 : ℝ) (812482901006947 / 500000000000000000 : ℝ) (328098693418413 / 10000000000000000 : ℝ)
    (cell12926 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · norm_num [cell12926]
  · have h := gap_lower (n := 12926) (a := (41027353902691 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444952210309 / 20000000000000 : ℝ))
      (E := (cell12926 ⟨59, by decide⟩).energy) (xi := (328098693418413 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12926 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12926]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12926])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12926) (a := (41027353902691 / 50000000000000 : ℝ)) (b := (3186399097 / 2000000000000 : ℝ)) (q := (444952210309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12926])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12926]

theorem cert12927_40 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (20673877793977 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (139035551921 / 6250000000000 : ℝ))
      (E := (cell12927 ⟨40, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (20673877793977 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (139035551921 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_41 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (2583174207671 / 3125000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112286404769 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨41, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (2583174207671 / 3125000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112286404769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_42 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82627661634317 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112288418707 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨42, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82627661634317 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112288418707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_43 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82593772112921 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (111229042721 / 5000000000000 : ℝ))
      (E := (cell12927 ⟨43, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82593772112921 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (111229042721 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_44 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (10319988256489 / 12500000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444916971833 / 20000000000000 : ℝ))
      (E := (cell12927 ⟨44, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (10319988256489 / 12500000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444916971833 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_45 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82526063422063 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224588850043 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨45, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82526063422063 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224588850043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_46 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82492244194297 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (111229644207 / 5000000000000 : ℝ))
      (E := (cell12927 ⟨46, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82492244194297 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (111229644207 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_47 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82458448339681 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444919380111 / 20000000000000 : ℝ))
      (E := (cell12927 ⟨47, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82458448339681 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444919380111 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_48 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82424675829427 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (27807511213 / 1250000000000 : ℝ))
      (E := (cell12927 ⟨48, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82424675829427 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (27807511213 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_49 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (20597731658723 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224604871129 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨49, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (20597731658723 / 25000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224604871129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_50 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (3294288029103 / 4000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (44492177583 / 2000000000000 : ℝ))
      (E := (cell12927 ⟨50, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (3294288029103 / 4000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (44492177583 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_51 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82323498079119 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224612918287 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨51, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82323498079119 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224612918287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_52 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82289818661309 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224616926461 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨52, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82289818661309 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224616926461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_53 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (8225616244607 / 10000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444924180073 / 20000000000000 : ℝ))
      (E := (cell12927 ⟨53, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (8225616244607 / 10000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444924180073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_54 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (41111264702733 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556156238669 / 25000000000000 : ℝ))
      (E := (cell12927 ⟨54, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (41111264702733 / 50000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (556156238669 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_55 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82188919511703 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224628967569 / 100000000000000 : ℝ))
      (E := (cell12927 ⟨55, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82188919511703 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (2224628967569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_56 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82155332737123 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (278079116889 / 12500000000000 : ℝ))
      (E := (cell12927 ⟨56, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82155332737123 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (278079116889 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_57 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82121769054207 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (4449273943 / 200000000000 : ℝ))
      (E := (cell12927 ⟨57, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82121769054207 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (4449273943 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_58 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (82088228435573 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444928190829 / 20000000000000 : ℝ))
      (E := (cell12927 ⟨58, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (82088228435573 / 100000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (444928190829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12927_59 : CellCertificate 12927 (880455820451661 / 10000000000000000 : ℝ) (1624840058167961 / 1000000000000000000 : ℝ) (164036357684511 / 5000000000000000 : ℝ)
    (cell12927 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · norm_num [cell12927]
  · have h := gap_lower (n := 12927) (a := (3282188434159 / 4000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112322498463 / 50000000000000 : ℝ))
      (E := (cell12927 ⟨59, by decide⟩).energy) (xi := (164036357684511 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12927 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12927]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12927])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12927) (a := (3282188434159 / 4000000000000 : ℝ)) (b := (79653742637 / 50000000000000 : ℝ)) (q := (1112322498463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12927])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12927]

theorem cert12928_40 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41347754348751 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112226390677 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨40, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41347754348751 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112226390677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_41 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82661572461583 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112228412459 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨41, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82661572461583 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112228412459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_42 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82627659744539 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224460800653 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨42, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82627659744539 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224460800653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_43 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (1651875410337 / 2000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224464824991 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨43, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (1651875410337 / 2000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224464824991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_44 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82559904749143 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224468837749 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨44, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82559904749143 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224468837749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_45 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82526062412193 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224472837319 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨45, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82526062412193 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224472837319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_46 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (20623060869231 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556119205469 / 25000000000000 : ℝ))
      (E := (cell12928 ⟨46, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (20623060869231 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (556119205469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_47 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41229223957201 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224480848317 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨47, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41229223957201 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224480848317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_48 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (515154223099 / 625000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (444896971101 / 20000000000000 : ℝ))
      (E := (cell12928 ⟨48, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (515154223099 / 625000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (444896971101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_49 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82390926792597 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112244420487 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨49, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82390926792597 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112244420487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_50 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82357201176173 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224492861051 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨50, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82357201176173 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224492861051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_51 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82323498818211 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224496853891 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨51, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82323498818211 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224496853891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_52 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (160722304083 / 195312500000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (278062609431 / 12500000000000 : ℝ))
      (E := (cell12928 ⟨52, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (160722304083 / 195312500000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (278062609431 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_53 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (41128081882477 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112252461241 / 50000000000000 : ℝ))
      (E := (cell12928 ⟨53, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (41128081882477 / 50000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (1112252461241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_54 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (1644450620273 / 2000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (44490178649 / 2000000000000 : ℝ))
      (E := (cell12928 ⟨54, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (1644450620273 / 2000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (44490178649 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_55 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82188921408791 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (278064112703 / 12500000000000 : ℝ))
      (E := (cell12928 ⟨55, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82188921408791 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (278064112703 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_56 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82155334922719 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224516944363 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨56, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82155334922719 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224516944363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_57 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (20530442881979 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224520938329 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨57, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (20530442881979 / 25000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224520938329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_58 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82088231197 / 100000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224524938369 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨58, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82088231197 / 100000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224524938369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12928_59 : CellCertificate 12928 (880428819356003 / 10000000000000000 : ℝ) (203089291722657 / 125000000000000000 : ℝ) (328046741473211 / 10000000000000000 : ℝ)
    (cell12928 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · norm_num [cell12928]
  · have h := gap_lower (n := 12928) (a := (82054713902727 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224528939999 / 100000000000000 : ℝ))
      (E := (cell12928 ⟨59, by decide⟩).energy) (xi := (328046741473211 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12928 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12928]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12928])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12928) (a := (82054713902727 / 100000000000000 : ℝ)) (b := (7964750883 / 5000000000000 : ℝ)) (q := (2224528939999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12928])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12928]

theorem cert12929_40 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82695506219911 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224336787763 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨40, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82695506219911 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224336787763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_41 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41330785139237 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556085194641 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨41, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41330785139237 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556085194641 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_42 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82627657855507 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224344819801 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨42, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82627657855507 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224344819801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_43 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82593768921489 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556087198173 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨43, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82593768921489 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556087198173 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_44 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (1651198068941 / 2000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224352813497 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨44, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (1651198068941 / 2000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224352813497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_45 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (20631515350741 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444871364359 / 20000000000000 : ℝ))
      (E := (cell12929 ⟨45, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (20631515350741 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444871364359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_46 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (20623060690039 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224360815759 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨46, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (20623060690039 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224360815759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_47 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82458447489693 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444872970457 / 20000000000000 : ℝ))
      (E := (cell12929 ⟨47, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82458447489693 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (444872970457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_48 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82424675562791 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224368870233 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨48, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82424675562791 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224368870233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_49 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (16478185390161 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224372867141 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨49, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (16478185390161 / 20000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224372867141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_50 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82357201625239 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556094224833 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨50, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82357201625239 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556094224833 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_51 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (10290437444717 / 12500000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224380904963 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨51, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (10290437444717 / 12500000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224380904963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_52 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82289820720081 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112192440467 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨52, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82289820720081 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112192440467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_53 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (41128082542101 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224388883009 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨53, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (41128082542101 / 50000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224388883009 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_54 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (20555633155541 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112196453871 / 50000000000000 : ℝ))
      (E := (cell12929 ⟨54, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (20555633155541 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (1112196453871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_55 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82188923306173 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556099223089 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨55, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82188923306173 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556099223089 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_56 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (3286213484343 / 4000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556100237801 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨56, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (3286213484343 / 4000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556100237801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_57 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82121774001851 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224404961951 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨57, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82121774001851 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224404961951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_58 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (82088233958619 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556102244861 / 25000000000000 : ℝ))
      (E := (cell12929 ⟨58, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (82088233958619 / 100000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (556102244861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12929_59 : CellCertificate 12929 (176080364452749 / 2000000000000000 : ℝ) (812294314424631 / 500000000000000000 : ℝ) (328020771729917 / 10000000000000000 : ℝ)
    (cell12929 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · norm_num [cell12929]
  · have h := gap_lower (n := 12929) (a := (20513679237909 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224412939983 / 100000000000000 : ℝ))
      (E := (cell12929 ⟨59, by decide⟩).energy) (xi := (328020771729917 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12929 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12929]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12929])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12929) (a := (20513679237909 / 25000000000000 : ℝ)) (b := (159282552007 / 100000000000000 : ℝ)) (q := (2224412939983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12929])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12929]

theorem cert12930_40 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (2584234491973 / 3125000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224220791193 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨40, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (2584234491973 / 3125000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224220791193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_41 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41330784048073 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224224846851 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨41, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41330784048073 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224224846851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_42 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (4131382798361 / 5000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224228836043 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨42, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (4131382798361 / 5000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224228836043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_43 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82593767326839 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224232816361 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨43, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82593767326839 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224232816361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_44 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (2579996942051 / 3125000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112118422637 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨44, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (2579996942051 / 3125000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112118422637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_45 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (10315757549297 / 12500000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112120431179 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨45, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (10315757549297 / 12500000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112120431179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_46 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (41246121021997 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224244865787 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨46, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (41246121021997 / 50000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224244865787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_47 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (20614611766389 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556062213381 / 25000000000000 : ℝ))
      (E := (cell12930 ⟨47, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (20614611766389 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (556062213381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_48 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82424675430277 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (222425288227 / 10000000000000 : ℝ))
      (E := (cell12930 ⟨48, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82424675430277 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (222425288227 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_49 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (16478185421903 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224256890651 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨49, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (16478185421903 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224256890651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_50 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (20589300518693 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224260875989 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨50, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (20589300518693 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224260875989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_51 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82323500297693 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224264894421 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨51, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82323500297693 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224264894421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_52 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (16457964350013 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112134471459 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨52, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (16457964350013 / 20000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112134471459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_53 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82256166403813 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (444854580019 / 20000000000000 : ℝ))
      (E := (cell12930 ⟨53, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82256166403813 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (444854580019 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_54 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82222534231007 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224276939651 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨54, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82222534231007 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224276939651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_55 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82188925203851 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224280939761 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨55, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82188925203851 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224280939761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_56 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (20538834823673 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112142477817 / 50000000000000 : ℝ))
      (E := (cell12930 ⟨56, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (20538834823673 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (1112142477817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_57 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (20530444119003 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224288983199 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨57, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (20530444119003 / 25000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224288983199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_58 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (82088236720431 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224292958987 / 100000000000000 : ℝ))
      (E := (cell12930 ⟨58, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (82088236720431 / 100000000000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (2224292958987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12930_59 : CellCertificate 12930 (440187414586977 / 5000000000000000 : ℝ) (203057867920933 / 125000000000000000 : ℝ) (13119792245523 / 400000000000000 : ℝ)
    (cell12930 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · norm_num [cell12930]
  · have h := gap_lower (n := 12930) (a := (1282105000011 / 1562500000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (711775039 / 32000000000 : ℝ))
      (E := (cell12930 ⟨59, by decide⟩).energy) (xi := (13119792245523 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12930 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12930]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12930])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12930) (a := (1282105000011 / 1562500000000 : ℝ)) (b := (31854017663 / 20000000000000 : ℝ)) (q := (711775039 / 32000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12930])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12930]

theorem cert12931_40 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82695501267177 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (139006553151 / 6250000000000 : ℝ))
      (E := (cell12931 ⟨40, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82695501267177 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (139006553151 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_41 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41330782957299 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224108853407 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨41, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41330782957299 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224108853407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_42 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82627654079679 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224112908197 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨42, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82627654079679 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224112908197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_43 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82593765732899 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224116896001 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨43, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82593765732899 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224116896001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_44 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (8255990084489 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112060437109 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨44, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (8255990084489 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112060437109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_45 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (20631514846607 / 25000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556031225031 / 25000000000000 : ℝ))
      (E := (cell12931 ⟨45, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (20631514846607 / 25000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556031225031 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_46 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41246120664219 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (444825782611 / 20000000000000 : ℝ))
      (E := (cell12931 ⟨46, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41246120664219 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (444825782611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_47 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (8245844664199 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (222413291097 / 10000000000000 : ℝ))
      (E := (cell12931 ⟨47, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (8245844664199 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (222413291097 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_48 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (824246752983 / 1000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556034237643 / 25000000000000 : ℝ))
      (E := (cell12931 ⟨48, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (824246752983 / 1000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556034237643 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_49 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82390927268727 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112070485243 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨49, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82390927268727 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112070485243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_50 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82357202524773 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (69504530251 / 3125000000000 : ℝ))
      (E := (cell12931 ⟨50, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82357202524773 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (69504530251 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_51 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82323501038083 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224148940323 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨51, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82323501038083 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224148940323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_52 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (41144911390223 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (444830588661 / 20000000000000 : ℝ))
      (E := (cell12931 ⟨52, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (41144911390223 / 50000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (444830588661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_53 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82256167723789 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (111207848687 / 5000000000000 : ℝ))
      (E := (cell12931 ⟨53, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82256167723789 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (111207848687 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_54 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82222535840179 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112080484541 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨54, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82222535840179 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112080484541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_55 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (642100992983 / 781250000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556041246181 / 25000000000000 : ℝ))
      (E := (cell12931 ⟨55, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (642100992983 / 781250000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (556041246181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_56 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (8215534148107 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2780211271 / 125000000000 : ℝ))
      (E := (cell12931 ⟨56, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (8215534148107 / 10000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2780211271 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_57 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82121778950401 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224173002071 / 100000000000000 : ℝ))
      (E := (cell12931 ⟨57, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82121778950401 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (2224173002071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_58 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (16417647896487 / 20000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112088527287 / 50000000000000 : ℝ))
      (E := (cell12931 ⟨58, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (16417647896487 / 20000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (1112088527287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12931_59 : CellCertificate 12931 (13755435001339 / 156250000000000 : ℝ) (406084319332837 / 250000000000000000 : ℝ) (327968844696621 / 10000000000000000 : ℝ)
    (cell12931 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · norm_num [cell12931]
  · have h := gap_lower (n := 12931) (a := (82054723049931 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (278022631433 / 12500000000000 : ℝ))
      (E := (cell12931 ⟨59, by decide⟩).energy) (xi := (327968844696621 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12931 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12931]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12931])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12931) (a := (82054723049931 / 100000000000000 : ℝ)) (b := (79628813291 / 50000000000000 : ℝ)) (q := (278022631433 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12931])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12931]

theorem cert12932_40 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (2584234337251 / 3125000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (277998620679 / 12500000000000 : ℝ))
      (E := (cell12932 ⟨40, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (2584234337251 / 3125000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (277998620679 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_41 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (8266156373383 / 10000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111996487303 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨41, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (8266156373383 / 10000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1111996487303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_42 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41313826096441 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444799395489 / 20000000000000 : ℝ))
      (E := (cell12932 ⟨42, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41313826096441 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444799395489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_43 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (82593764139669 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (556000243193 / 25000000000000 : ℝ))
      (E := (cell12932 ⟨43, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (82593764139669 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (556000243193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_44 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (82559899544823 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (222400495919 / 10000000000000 : ℝ))
      (E := (cell12932 ⟨44, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (82559899544823 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (222400495919 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_45 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (82526058379121 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1112004496989 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨45, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (82526058379121 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1112004496989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_46 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (5155765038343 / 6250000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2224013016469 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨46, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (5155765038343 / 6250000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2224013016469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_47 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16491689243799 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1112008512311 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨47, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16491689243799 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1112008512311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_48 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (82424675166859 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2224021016183 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨48, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (82424675166859 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2224021016183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_49 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (2059773185711 / 2500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (139001565479 / 6250000000000 : ℝ))
      (E := (cell12932 ⟨49, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (2059773185711 / 2500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (139001565479 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_50 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (2058930074381 / 2500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (139001816091 / 6250000000000 : ℝ))
      (E := (cell12932 ⟨50, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (2058930074381 / 2500000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (139001816091 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_51 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41161750889453 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444806608533 / 20000000000000 : ℝ))
      (E := (cell12932 ⟨51, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41161750889453 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (444806608533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_52 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (41144911905613 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2224037059241 / 100000000000000 : ℝ))
      (E := (cell12932 ⟨52, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (41144911905613 / 50000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (2224037059241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_53 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (2570505282629 / 3125000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (222404104487 / 10000000000000 : ℝ))
      (E := (cell12932 ⟨53, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (2570505282629 / 3125000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (222404104487 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_54 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (1027781718121 / 1250000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (222404505513 / 10000000000000 : ℝ))
      (E := (cell12932 ⟨54, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (1027781718121 / 1250000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (222404505513 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_55 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (20547232250023 / 25000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1112024543181 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨55, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (20547232250023 / 25000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1112024543181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_56 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (82155343667709 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (556013268889 / 25000000000000 : ℝ))
      (E := (cell12932 ⟨56, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (82155343667709 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (556013268889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_57 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16424356285003 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1112028538869 / 50000000000000 : ℝ))
      (E := (cell12932 ⟨57, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16424356285003 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (1112028538869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_58 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (82088242244631 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (222406108863 / 10000000000000 : ℝ))
      (E := (cell12932 ⟨58, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (82088242244631 / 100000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (222406108863 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12932_59 : CellCertificate 12932 (880320854998039 / 10000000000000000 : ℝ) (1624211630736401 / 1000000000000000000 : ℝ) (65588577480899 / 2000000000000000 : ℝ)
    (cell12932 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · norm_num [cell12932]
  · have h := gap_lower (n := 12932) (a := (16410945219863 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (556016275937 / 25000000000000 : ℝ))
      (E := (cell12932 ⟨59, by decide⟩).energy) (xi := (65588577480899 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12932 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12932]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12932])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12932) (a := (16410945219863 / 20000000000000 : ℝ)) (b := (15924516681 / 10000000000000 : ℝ)) (q := (556016275937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12932])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12932]

theorem cert12933_40 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41347748158851 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223873018703 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨40, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41347748158851 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223873018703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_41 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41330780776921 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111938517037 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨41, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41330780776921 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111938517037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_42 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (8262765030683 / 10000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (222388104379 / 10000000000000 : ℝ))
      (E := (cell12933 ⟨42, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (8262765030683 / 10000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (222388104379 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_43 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82593762547149 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (88955401867 / 4000000000000 : ℝ))
      (E := (cell12933 ⟨43, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82593762547149 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (88955401867 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_44 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82559898245431 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111944550097 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨44, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82559898245431 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111944550097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_45 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82526057372453 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555973271259 / 25000000000000 : ℝ))
      (E := (cell12933 ⟨45, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82526057372453 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (555973271259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_46 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82492239899143 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111948558561 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨46, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82492239899143 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111948558561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_47 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82458445796571 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (444780215323 / 20000000000000 : ℝ))
      (E := (cell12933 ⟨47, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82458445796571 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (444780215323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_48 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41212337517977 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223905138061 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨48, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41212337517977 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223905138061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_49 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41195463794327 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223909122189 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨49, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41195463794327 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223909122189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_50 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (41178601713087 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (111195657213 / 5000000000000 : ℝ))
      (E := (cell12933 ⟨50, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (41178601713087 / 50000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (111195657213 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_51 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82323502520161 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223917142423 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨51, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82323502520161 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223917142423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_52 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82289824842403 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223921172629 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨52, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82289824842403 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223921172629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_53 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (8225617036483 / 10000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111962586281 / 50000000000000 : ℝ))
      (E := (cell12933 ⟨53, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (8225617036483 / 10000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (1111962586281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_54 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82222539059511 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (22239291387 / 1000000000000 : ℝ))
      (E := (cell12933 ⟨54, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82222539059511 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (22239291387 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_55 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (16437786179731 / 20000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223933185557 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨55, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (16437786179731 / 20000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223933185557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_56 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (5134709115913 / 6250000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223937191049 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨56, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (5134709115913 / 6250000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223937191049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_57 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (5132611493741 / 6250000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (11119706051 / 500000000000 : ℝ))
      (E := (cell12933 ⟨57, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (5132611493741 / 6250000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (11119706051 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_58 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (4104412250351 / 5000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223945179539 / 100000000000000 : ℝ))
      (E := (cell12933 ⟨58, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (4104412250351 / 5000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (2223945179539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12933_59 : CellCertificate 12933 (17605877478201 / 200000000000000 : ℝ) (1624086003578113 / 1000000000000000000 : ℝ) (327916934260631 / 10000000000000000 : ℝ)
    (cell12933 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · norm_num [cell12933]
  · have h := gap_lower (n := 12933) (a := (82054729148857 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (138996825809 / 6250000000000 : ℝ))
      (E := (cell12933 ⟨59, by decide⟩).energy) (xi := (327916934260631 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12933 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12933]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12933])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12933) (a := (82054729148857 / 100000000000000 : ℝ)) (b := (159232708997 / 100000000000000 : ℝ)) (q := (138996825809 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12933])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12933]

theorem cert12934_40 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41347746922093 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223757186539 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨40, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41347746922093 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223757186539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_41 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82661559374633 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555940302047 / 25000000000000 : ℝ))
      (E := (cell12934 ⟨41, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82661559374633 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555940302047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_42 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82627648421523 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (69492661439 / 3125000000000 : ℝ))
      (E := (cell12934 ⟨42, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82627648421523 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (69492661439 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_43 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82593760955339 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223769176549 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨43, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82593760955339 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223769176549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_44 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82559896946713 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (138985823719 / 6250000000000 : ℝ))
      (E := (cell12934 ⟨44, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82559896946713 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (138985823719 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_45 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41263028183213 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (277972154023 / 12500000000000 : ℝ))
      (E := (cell12934 ⟨45, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41263028183213 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (277972154023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_46 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82492239185403 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444756243003 / 20000000000000 : ℝ))
      (E := (cell12934 ⟨46, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82492239185403 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444756243003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_47 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82458445374717 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223785243751 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨47, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82458445374717 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223785243751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_48 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (16484934981117 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223789257249 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨48, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (16484934981117 / 20000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223789257249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_49 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (8239092774937 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (27797415663 / 1250000000000 : ℝ))
      (E := (cell12934 ⟨49, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (8239092774937 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (27797415663 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_50 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (3294288155103 / 4000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444759445689 / 20000000000000 : ℝ))
      (E := (cell12934 ⟨50, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (3294288155103 / 4000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444759445689 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_51 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (10290437907731 / 12500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223801239599 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨51, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (10290437907731 / 12500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223801239599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_52 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41144912936989 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223805283469 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨52, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41144912936989 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223805283469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_53 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (10282021460737 / 12500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (111190464887 / 5000000000000 : ℝ))
      (E := (cell12934 ⟨53, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (10282021460737 / 12500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (111190464887 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_54 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (8222254066967 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222381327889 / 10000000000000 : ℝ))
      (E := (cell12934 ⟨54, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (8222254066967 / 10000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222381327889 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_55 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (10273616599689 / 12500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222381728231 / 10000000000000 : ℝ))
      (E := (cell12934 ⟨55, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (10273616599689 / 12500000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (222381728231 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_56 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82155348041767 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444764260827 / 20000000000000 : ℝ))
      (E := (cell12934 ⟨56, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82155348041767 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (444764260827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_57 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (82121786374923 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223825340289 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨57, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (82121786374923 / 100000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223825340289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_58 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (6413144357 / 7812500000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223829327303 / 100000000000000 : ℝ))
      (E := (cell12934 ⟨58, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (6413144357 / 7812500000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (2223829327303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12934_59 : CellCertificate 12934 (220066724205199 / 2500000000000000 : ℝ) (1623960395851973 / 1000000000000000000 : ℝ) (32789098526397 / 1000000000000000 : ℝ)
    (cell12934 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · norm_num [cell12934]
  · have h := gap_lower (n := 12934) (a := (41027366099279 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555958329959 / 25000000000000 : ℝ))
      (E := (cell12934 ⟨59, by decide⟩).energy) (xi := (32789098526397 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12934 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12934]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12934])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12934) (a := (41027366099279 / 50000000000000 : ℝ)) (b := (159220253143 / 100000000000000 : ℝ)) (q := (555958329959 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12934])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12934]

theorem cert12935_40 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (16539098274297 / 20000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (11118206757 / 500000000000 : ℝ))
      (E := (cell12935 ⟨40, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (16539098274297 / 20000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (11118206757 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_41 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (20665389299051 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223645320571 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨41, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (20665389299051 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223645320571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_42 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (64552848857 / 78125000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (111182467211 / 5000000000000 : ℝ))
      (E := (cell12935 ⟨42, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (64552848857 / 78125000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (111182467211 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_43 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41296879682119 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111826681199 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨43, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41296879682119 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111826681199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_44 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (8255989564867 / 10000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223657373709 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨44, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (8255989564867 / 10000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223657373709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_45 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41263027680519 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111830688269 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨45, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41263027680519 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111830688269 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_46 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (20623059618067 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223665369059 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨46, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (20623059618067 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223665369059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_47 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (82458444953433 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223669408163 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨47, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (82458444953433 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223669408163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_48 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (10303084346969 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (555918343437 / 25000000000000 : ℝ))
      (E := (cell12935 ⟨48, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (10303084346969 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (555918343437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_49 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41195463955293 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111838690619 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨49, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41195463955293 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111838690619 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_50 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (41178602164721 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223681428021 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨50, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (41178602164721 / 50000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223681428021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_51 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (82323504003967 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223685393219 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨51, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (82323504003967 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223685393219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_52 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (82289826905951 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223689450813 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨52, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (82289826905951 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223689450813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_53 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (20564043251831 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223693420407 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨53, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (20564043251831 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223693420407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_54 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (82222542280159 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223697475701 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨54, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (82222542280159 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223697475701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_55 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (82188934696663 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223701435743 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨55, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (82188934696663 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223701435743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_56 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (82155350229187 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111852736979 / 50000000000000 : ℝ))
      (E := (cell12935 ⟨56, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (82155350229187 / 100000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (1111852736979 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_57 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (10265223606277 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223709468007 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨57, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (10265223606277 / 12500000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223709468007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_58 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (20522062633093 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (222371347273 / 10000000000000 : ℝ))
      (E := (cell12935 ⟨58, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (20522062633093 / 25000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (222371347273 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12935_59 : CellCertificate 12935 (176047984745869 / 2000000000000000 : ℝ) (1623834807553473 / 1000000000000000000 : ℝ) (327865040413449 / 10000000000000000 : ℝ)
    (cell12935 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · norm_num [cell12935]
  · have h := gap_lower (n := 12935) (a := (16410947049683 / 20000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223717483643 / 100000000000000 : ℝ))
      (E := (cell12935 ⟨59, by decide⟩).energy) (xi := (327865040413449 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12935 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12935]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12935])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12935) (a := (16410947049683 / 20000000000000 : ℝ)) (b := (159207799247 / 100000000000000 : ℝ)) (q := (2223717483643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12935])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12935]

theorem cert12936_40 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41347744449799 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223525513289 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨40, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41347744449799 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223525513289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_41 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41330777509277 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (222352948881 / 10000000000000 : ℝ))
      (E := (cell12936 ⟨41, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41330777509277 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (222352948881 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_42 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82627644653141 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223533519491 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨42, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82627644653141 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223533519491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_43 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41296878886923 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223537545381 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨43, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41296878886923 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223537545381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_44 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41279947175651 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (111177075311 / 5000000000000 : ℝ))
      (E := (cell12936 ⟨44, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41279947175651 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (111177075311 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_45 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (8252605435629 / 10000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223545518097 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨45, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (8252605435629 / 10000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223545518097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_46 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41246118879869 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111774789627 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨46, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41246118879869 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111774789627 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_47 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (1030730556659 / 1250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223553569851 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨47, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (1030730556659 / 1250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223553569851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_48 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41212337323227 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223557546517 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨48, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41212337323227 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223557546517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_49 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (5149433004519 / 6250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555890391441 / 25000000000000 : ℝ))
      (E := (cell12936 ⟨49, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (5149433004519 / 6250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555890391441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_50 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (3294288191271 / 4000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (277945695747 / 12500000000000 : ℝ))
      (E := (cell12936 ⟨50, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (3294288191271 / 4000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (277945695747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_51 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82323504746517 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111784801643 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨51, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82323504746517 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111784801643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_52 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (1028622849229 / 1250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223573615611 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨52, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (1028622849229 / 1250000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223573615611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_53 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (20564043582279 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555894399909 / 25000000000000 : ℝ))
      (E := (cell12936 ⟨53, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (20564043582279 / 25000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (555894399909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_54 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (3288901755639 / 4000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223581610939 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨54, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (3288901755639 / 4000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223581610939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_55 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82188936596109 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (69487051433 / 3125000000000 : ℝ))
      (E := (cell12936 ⟨55, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82188936596109 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (69487051433 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_56 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82155352416867 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (69487176293 / 3125000000000 : ℝ))
      (E := (cell12936 ⟨56, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82155352416867 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (69487176293 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_57 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (41060895662867 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111796826261 / 50000000000000 : ℝ))
      (E := (cell12936 ⟨57, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (41060895662867 / 50000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (1111796826261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_58 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (10261031661917 / 12500000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223597675013 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨58, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (10261031661917 / 12500000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223597675013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12936_59 : CellCertificate 12936 (440106477317383 / 5000000000000000 : ℝ) (1623709238678107 / 1000000000000000000 : ℝ) (40979887463501 / 1250000000000000 : ℝ)
    (cell12936 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · norm_num [cell12936]
  · have h := gap_lower (n := 12936) (a := (82054738298431 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223601704363 / 100000000000000 : ℝ))
      (E := (cell12936 ⟨59, by decide⟩).energy) (xi := (40979887463501 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12936 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12936]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12936])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12936) (a := (82054738298431 / 100000000000000 : ℝ)) (b := (159195347309 / 100000000000000 : ℝ)) (q := (2223601704363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12936])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12936]

theorem cert12937_40 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (3307819457141 / 4000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (88936389239 / 4000000000000 : ℝ))
      (E := (cell12937 ⟨40, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (3307819457141 / 4000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (88936389239 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_41 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41330776420841 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223413712907 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨41, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41330776420841 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223413712907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_42 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41313821385033 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111708875339 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨42, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41313821385033 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111708875339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_43 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82593756184163 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (4446843451 / 200000000000 : ℝ))
      (E := (cell12937 ⟨43, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82593756184163 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (4446843451 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_44 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (5159993315913 / 6250000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223425753629 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨44, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (5159993315913 / 6250000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223425753629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_45 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82526053352181 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223429774637 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨45, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82526053352181 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223429774637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_46 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (20623059261953 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111716863891 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨46, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (20623059261953 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111716863891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_47 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (1288413189259 / 1562500000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223437787751 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨47, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (1288413189259 / 1562500000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223437787751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_48 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82424674517691 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223441775557 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨48, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82424674517691 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223441775557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_49 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41195464117261 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223445806619 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨49, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41195464117261 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223445806619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_50 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (3294288209383 / 4000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111724909661 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨50, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (3294288209383 / 4000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111724909661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_51 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82323505489499 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (555863452693 / 25000000000000 : ℝ))
      (E := (cell12937 ⟨51, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82323505489499 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (555863452693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_52 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82289828971087 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111728918457 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨52, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82289828971087 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111728918457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_53 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (8225617565127 / 10000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223461835431 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨53, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (8225617565127 / 10000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223461835431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_54 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82222545502121 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111732901399 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨54, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82222545502121 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111732901399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_55 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82188938495849 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223469853529 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨55, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82188938495849 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223469853529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_56 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (41077677302403 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111736932767 / 50000000000000 : ℝ))
      (E := (cell12937 ⟨56, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (41077677302403 / 50000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (1111736932767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_57 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82121793801479 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223477834667 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨57, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82121793801479 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223477834667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_58 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (82088256058491 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223481874961 / 100000000000000 : ℝ))
      (E := (cell12937 ⟨58, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (82088256058491 / 100000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (2223481874961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12937_59 : CellCertificate 12937 (880185989536127 / 10000000000000000 : ℝ) (1623583689221369 / 1000000000000000000 : ℝ) (65562632629317 / 2000000000000000 : ℝ)
    (cell12937 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · norm_num [cell12937]
  · have h := gap_lower (n := 12937) (a := (20513685337151 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (138967866473 / 6250000000000 : ℝ))
      (E := (cell12937 ⟨59, by decide⟩).energy) (xi := (65562632629317 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12937 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12937]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12937])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12937) (a := (20513685337151 / 25000000000000 : ℝ)) (b := (9948931083 / 6250000000000 : ℝ)) (q := (138967866473 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12937])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12937]

theorem cert12938_40 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (16539096791653 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223293945691 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨40, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (16539096791653 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223293945691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_41 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82661550665589 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223297934067 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨41, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82661550665589 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223297934067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_42 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (16525528177547 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223301920149 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨42, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (16525528177547 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223301920149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_43 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82593754595189 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111652980797 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨43, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82593754595189 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111652980797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_44 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82559891758587 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223309939347 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨44, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82559891758587 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223309939347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_45 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82526052348711 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223313969497 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨45, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82526052348711 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223313969497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_46 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82492236336491 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (555829497843 / 25000000000000 : ℝ))
      (E := (cell12938 ⟨46, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82492236336491 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (555829497843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_47 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41229221846501 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223322002929 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨47, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41229221846501 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223322002929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_48 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82424674389463 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223326001911 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨48, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82424674389463 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223326001911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_49 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (2059773209931 / 2500000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (555832496461 / 25000000000000 : ℝ))
      (E := (cell12938 ⟨49, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (2059773209931 / 2500000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (555832496461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_50 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (514732535549 / 625000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (44466680221 / 2000000000000 : ℝ))
      (E := (cell12938 ⟨50, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (514732535549 / 625000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (44466680221 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_51 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82323506232913 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223338015677 / 100000000000000 : ℝ))
      (E := (cell12938 ⟨51, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82323506232913 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (2223338015677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_52 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82289830004251 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (277917756959 / 12500000000000 : ℝ))
      (E := (cell12938 ⟨52, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82289830004251 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (277917756959 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_53 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (20564044243447 / 25000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111673034357 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨53, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (20564044243447 / 25000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111673034357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_54 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41111273556797 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111675025641 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨54, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41111273556797 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111675025641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_55 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82188940395883 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111677029381 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨55, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82188940395883 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111677029381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_56 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41077678396503 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111679043643 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨56, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41077678396503 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111679043643 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_57 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (82121796277449 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (222336207361 / 10000000000000 : ℝ))
      (E := (cell12938 ⟨57, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (82121796277449 / 100000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (222336207361 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_58 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (41044129410919 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111683036287 / 50000000000000 : ℝ))
      (E := (cell12938 ⟨58, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (41044129410919 / 50000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (1111683036287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12938_59 : CellCertificate 12938 (55009939277031 / 625000000000000 : ℝ) (811729079589377 / 500000000000000000 : ℝ) (327787230728121 / 10000000000000000 : ℝ)
    (cell12938 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · norm_num [cell12938]
  · have h := gap_lower (n := 12938) (a := (16410948879787 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (277921259961 / 12500000000000 : ℝ))
      (E := (cell12938 ⟨59, by decide⟩).energy) (xi := (327787230728121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12938 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12938]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12938])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12938) (a := (16410948879787 / 20000000000000 : ℝ)) (b := (19896306163 / 12500000000000 : ℝ)) (q := (277921259961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12938])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12938]

theorem cert12939_40 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82695481488819 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444635631487 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨40, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82695481488819 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444635631487 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_41 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41330774245137 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223182211087 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨41, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41330774245137 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223182211087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_42 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82627639006147 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111593102177 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨42, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82627639006147 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111593102177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_43 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (20648438251731 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (88927607793 / 4000000000000 : ℝ))
      (E := (cell12939 ⟨43, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (20648438251731 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (88927607793 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_44 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (2063997261581 / 2500000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444638847993 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨44, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (2063997261581 / 2500000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444638847993 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_45 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82526051345881 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223198220451 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨45, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82526051345881 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223198220451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_46 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41246117812887 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223202252207 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨46, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41246117812887 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223202252207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_47 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82458443273997 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (555801553847 / 25000000000000 : ℝ))
      (E := (cell12939 ⟨47, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82458443273997 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (555801553847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_48 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (8242467426177 / 10000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223210225579 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨48, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (8242467426177 / 10000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223210225579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_49 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82390928560459 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223214280379 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨49, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82390928560459 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223214280379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_50 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82357206141571 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223218259167 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨50, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82357206141571 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223218259167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_51 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41161753488379 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (277902784629 / 12500000000000 : ℝ))
      (E := (cell12939 ⟨51, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41161753488379 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (277902784629 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_52 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (20572457759453 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111613135943 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨52, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (20572457759453 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111613135943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_53 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82256178296667 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (222323029949 / 10000000000000 : ℝ))
      (E := (cell12939 ⟨53, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82256178296667 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (222323029949 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_54 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (20555637181349 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223234297291 / 100000000000000 : ℝ))
      (E := (cell12939 ⟨54, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (20555637181349 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (2223234297291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_55 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (82188942296211 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111619160339 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨55, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (82188942296211 / 100000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111619160339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_56 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (16431071796293 / 20000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444648461327 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨56, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (16431071796293 / 20000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444648461327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_57 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (20530449688411 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111623155093 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨57, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (20530449688411 / 25000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111623155093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_58 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (2565258174543 / 3125000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444650065409 / 20000000000000 : ℝ))
      (E := (cell12939 ⟨58, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (2565258174543 / 3125000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (444650065409 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12939_59 : CellCertificate 12939 (13752063614421 / 156250000000000 : ℝ) (10145829053411 / 6250000000000000 : ℝ) (65552260490311 / 2000000000000000 : ℝ)
    (cell12939 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · norm_num [cell12939]
  · have h := gap_lower (n := 12939) (a := (41027373724711 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111627176363 / 50000000000000 : ℝ))
      (E := (cell12939 ⟨59, by decide⟩).energy) (xi := (65552260490311 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12939 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12939]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12939])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12939) (a := (41027373724711 / 50000000000000 : ℝ)) (b := (39789500809 / 25000000000000 : ℝ)) (q := (1111627176363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12939])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12939]

theorem cert12940_40 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (16539095804037 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223062483751 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨40, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (16539095804037 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223062483751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_41 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41330773157869 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555766621293 / 25000000000000 : ℝ))
      (E := (cell12940 ⟨41, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41330773157869 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555766621293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_42 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41313818562651 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111535242831 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨42, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41313818562651 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111535242831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_43 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41296875709683 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (444614896807 / 20000000000000 : ℝ))
      (E := (cell12940 ⟨43, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41296875709683 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (444614896807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_44 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (82559889168567 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555769619723 / 25000000000000 : ℝ))
      (E := (cell12940 ⟨44, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (82559889168567 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555769619723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_45 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (82526050343689 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111541263751 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨45, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (82526050343689 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111541263751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_46 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (82492234915661 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111543255143 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨46, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (82492234915661 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111543255143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_47 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41229221427781 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223090542993 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨47, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41229221427781 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223090542993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_48 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (20606168533653 / 25000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (27788681319 / 1250000000000 : ℝ))
      (E := (cell12940 ⟨48, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (20606168533653 / 25000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (27788681319 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_49 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41195464362089 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (444619702657 / 20000000000000 : ℝ))
      (E := (cell12940 ⟨49, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41195464362089 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (444619702657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_50 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (10294650824471 / 12500000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111551281837 / 50000000000000 : ℝ))
      (E := (cell12940 ⟨50, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (10294650824471 / 12500000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (1111551281837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_51 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41161753860517 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223106535807 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨51, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41161753860517 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223106535807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_52 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (8228983207177 / 10000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (69472204519 / 3125000000000 : ℝ))
      (E := (cell12940 ⟨52, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (8228983207177 / 10000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (69472204519 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_53 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (82256179619909 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (138944661677 / 6250000000000 : ℝ))
      (E := (cell12940 ⟨53, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (82256179619909 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (138944661677 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_54 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41111275168763 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (88924743997 / 4000000000000 : ℝ))
      (E := (cell12940 ⟨54, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41111275168763 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (88924743997 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_55 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (82188944196833 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555780645039 / 25000000000000 : ℝ))
      (E := (cell12940 ⟨55, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (82188944196833 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (555780645039 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_56 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (82155361170183 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223126582727 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨56, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (82155361170183 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223126582727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_57 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (16424360246013 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223130603561 / 100000000000000 : ℝ))
      (E := (cell12940 ⟨57, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (16424360246013 / 20000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (2223130603561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_58 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (41044132174553 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (17785077107 / 800000000000 : ℝ))
      (E := (cell12940 ⟨58, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (41044132174553 / 50000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (17785077107 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12940_59 : CellCertificate 12940 (440052559103269 / 5000000000000000 : ℝ) (811603578658943 / 500000000000000000 : ℝ) (327735378315829 / 10000000000000000 : ℝ)
    (cell12940 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · norm_num [cell12940]
  · have h := gap_lower (n := 12940) (a := (82054750500067 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (277892327933 / 12500000000000 : ℝ))
      (E := (cell12940 ⟨59, by decide⟩).energy) (xi := (327735378315829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12940 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12940]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12940])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12940) (a := (82054750500067 / 100000000000000 : ℝ)) (b := (39786389781 / 25000000000000 : ℝ)) (q := (277892327933 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12940])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12940]

theorem cert12941_40 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (16539095310473 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111473374163 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨40, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (16539095310473 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111473374163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_41 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82661544141979 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (88918030253 / 4000000000000 : ℝ))
      (E := (cell12941 ⟨41, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82661544141979 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (88918030253 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_42 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (206569088113 / 250000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277869345509 / 12500000000000 : ℝ))
      (E := (cell12941 ⟨42, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (206569088113 / 250000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277869345509 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_43 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82593749832517 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111479385191 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨43, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82593749832517 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111479385191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_44 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82559887874567 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (69467586683 / 3125000000000 : ℝ))
      (E := (cell12941 ⟨44, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82559887874567 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (69467586683 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_45 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (16505209868427 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222966831763 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨45, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (16505209868427 / 20000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222966831763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_46 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (10311529275769 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (55574270613 / 2500000000000 : ℝ))
      (E := (cell12941 ⟨46, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (10311529275769 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (55574270613 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_47 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (1288413163089 / 1562500000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (138935925559 / 6250000000000 : ℝ))
      (E := (cell12941 ⟨47, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (1288413163089 / 1562500000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (138935925559 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_48 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82424674007989 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222978841733 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨48, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82424674007989 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222978841733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_49 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82390928888397 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111491430751 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨49, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82390928888397 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111491430751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_50 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (8235720705043 / 10000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (69468339549 / 3125000000000 : ℝ))
      (E := (cell12941 ⟨50, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (8235720705043 / 10000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (69468339549 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_51 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (41161754232871 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (222299085103 / 10000000000000 : ℝ))
      (E := (cell12941 ⟨51, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (41161754232871 / 50000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (222299085103 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_52 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (20572458276531 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222994873837 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨52, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (20572458276531 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2222994873837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_53 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82256180943513 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (444599774333 / 20000000000000 : ℝ))
      (E := (cell12941 ⟨53, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82256180943513 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (444599774333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_54 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82222551949983 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2223002900087 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨54, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82222551949983 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2223002900087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_55 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (20547236524437 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111503448159 / 50000000000000 : ℝ))
      (E := (cell12941 ⟨55, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (20547236524437 / 25000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (1111503448159 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_56 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82155363359161 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (55575272889 / 2500000000000 : ℝ))
      (E := (cell12941 ⟨56, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82155363359161 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (55575272889 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_57 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (10265225463339 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277876861821 / 12500000000000 : ℝ))
      (E := (cell12941 ⟨57, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (10265225463339 / 12500000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (277876861821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_58 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82088267113027 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2223018947371 / 100000000000000 : ℝ))
      (E := (cell12941 ⟨58, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82088267113027 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (2223018947371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12941_59 : CellCertificate 12941 (880078169082349 / 10000000000000000 : ℝ) (1623081685490631 / 1000000000000000000 : ℝ) (81927364579971 / 2500000000000000 : ℝ)
    (cell12941 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · norm_num [cell12941]
  · have h := gap_lower (n := 12941) (a := (82054753550869 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (27787786889 / 1250000000000 : ℝ))
      (E := (cell12941 ⟨59, by decide⟩).energy) (xi := (81927364579971 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12941 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12941]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12941])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12941) (a := (82054753550869 / 100000000000000 : ℝ)) (b := (19891639621 / 12500000000000 : ℝ)) (q := (27787786889 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12941])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12941]

theorem cert12942_40 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82695474085357 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222831068703 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨40, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82695474085357 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222831068703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_41 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41330770984499 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111417541669 / 50000000000000 : ℝ))
      (E := (cell12942 ⟨41, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41330770984499 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111417541669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_42 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82627633365841 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222839098401 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨42, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82627633365841 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222839098401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_43 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (10324218530797 / 12500000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555710778177 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨43, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (10324218530797 / 12500000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555710778177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_44 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (2063997164531 / 2500000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111423562429 / 50000000000000 : ℝ))
      (E := (cell12942 ⟨44, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (2063997164531 / 2500000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111423562429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_45 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (4126302417061 / 5000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222851133233 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨45, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (4126302417061 / 5000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222851133233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_46 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41246116748623 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (69464223 / 3125000000 : ℝ))
      (E := (cell12942 ⟨46, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41246116748623 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (69464223 / 3125000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_47 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82458442020399 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222859131111 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨47, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82458442020399 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222859131111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_48 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82424673881899 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (69464474227 / 3125000000000 : ℝ))
      (E := (cell12942 ⟨48, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82424673881899 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (69464474227 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_49 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (20597732263279 / 25000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222867148091 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨49, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (20597732263279 / 25000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222867148091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_50 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41178603752779 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (138929447803 / 6250000000000 : ℝ))
      (E := (cell12942 ⟨50, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41178603752779 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (138929447803 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_51 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (64315241571 / 78125000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222875163677 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨51, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (64315241571 / 78125000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222875163677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_52 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (658318673127 / 800000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555719800131 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨52, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (658318673127 / 800000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555719800131 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_53 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82256182267479 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222883213067 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨53, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82256182267479 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222883213067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_54 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82222553562769 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (138930449861 / 6250000000000 : ℝ))
      (E := (cell12942 ⟨54, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82222553562769 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (138930449861 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_55 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82188947998957 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111445605021 / 50000000000000 : ℝ))
      (E := (cell12942 ⟨55, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82188947998957 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111445605021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_56 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82155365548399 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222895245991 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨56, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82155365548399 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222895245991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_57 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82121806183583 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222899242377 / 100000000000000 : ℝ))
      (E := (cell12942 ⟨57, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82121806183583 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (2222899242377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_58 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (41044134938569 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555725813509 / 25000000000000 : ℝ))
      (E := (cell12942 ⟨58, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (41044134938569 / 50000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (555725813509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12942_59 : CellCertificate 12942 (880051223949447 / 10000000000000000 : ℝ) (1622956233059497 / 1000000000000000000 : ℝ) (16384177123133 / 500000000000000 : ℝ)
    (cell12942 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · norm_num [cell12942]
  · have h := gap_lower (n := 12942) (a := (82054756601829 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111453638239 / 50000000000000 : ℝ))
      (E := (cell12942 ⟨59, by decide⟩).energy) (xi := (16384177123133 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12942 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12942]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12942])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12942) (a := (82054756601829 / 100000000000000 : ℝ)) (b := (159120676767 / 100000000000000 : ℝ)) (q := (1111453638239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12942])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12942]

theorem cert12943_40 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41347735809581 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222715444883 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨40, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41347735809581 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222715444883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_41 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41330769898397 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111359733107 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨41, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41330769898397 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111359733107 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_42 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (3305105259489 / 4000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (555680872163 / 25000000000000 : ℝ))
      (E := (cell12943 ⟨42, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (3305105259489 / 4000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (555680872163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_43 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41296873330471 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (88909098087 / 4000000000000 : ℝ))
      (E := (cell12943 ⟨43, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41296873330471 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (88909098087 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_44 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41279942644293 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222731473037 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨44, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41279942644293 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222731473037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_45 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (82526047340943 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111367745401 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨45, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (82526047340943 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111367745401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_46 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (5155764549309 / 6250000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111369751819 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨46, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (5155764549309 / 6250000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111369751819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_47 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (8245844160367 / 10000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (444548701899 / 20000000000000 : ℝ))
      (E := (cell12943 ⟨47, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (8245844160367 / 10000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (444548701899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_48 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (10303084219543 / 12500000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (34730429783 / 1562500000000 : ℝ))
      (E := (cell12943 ⟨48, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (10303084219543 / 12500000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (34730429783 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_49 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41195464609167 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (555687887499 / 25000000000000 : ℝ))
      (E := (cell12943 ⟨49, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41195464609167 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (555687887499 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_50 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (82357207961151 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222755520521 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨50, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (82357207961151 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222755520521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_51 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (2572609686139 / 3125000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222759532777 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨51, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (2572609686139 / 3125000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222759532777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_52 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41144917588011 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222763524671 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨52, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41144917588011 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222763524671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_53 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (642626434311 / 781250000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222767551961 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨53, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (642626434311 / 781250000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222767551961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_54 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (41111277587941 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222771552093 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨54, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (41111277587941 / 50000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222771552093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_55 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (4109447495023 / 5000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222775580453 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨55, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (4109447495023 / 5000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222775580453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_56 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (16431073547579 / 20000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111389787011 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨56, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (16431073547579 / 20000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111389787011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_57 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (82121808660679 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222783587821 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨57, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (82121808660679 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222783587821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_58 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (82088272641441 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111393808781 / 50000000000000 : ℝ))
      (E := (cell12943 ⟨58, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (82088272641441 / 100000000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (1111393808781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12943_59 : CellCertificate 12943 (440012141403451 / 5000000000000000 : ℝ) (1622830800019987 / 1000000000000000000 : ℝ) (327657630743101 / 10000000000000000 : ℝ)
    (cell12943 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · norm_num [cell12943]
  · have h := gap_lower (n := 12943) (a := (5128422478309 / 6250000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222791599541 / 100000000000000 : ℝ))
      (E := (cell12943 ⟨59, by decide⟩).energy) (xi := (327657630743101 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12943 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12943]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12943])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12943) (a := (5128422478309 / 6250000000000 : ℝ)) (b := (3977705963 / 2500000000000 : ℝ)) (q := (2222791599541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12943])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12943]

theorem cert12944_40 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41347734576889 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111299909049 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨40, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41347734576889 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111299909049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_41 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (10332692203171 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111301923079 / 50000000000000 : ℝ))
      (E := (cell12944 ⟨41, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (10332692203171 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (1111301923079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_42 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (1652552592187 / 2000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (277825977149 / 12500000000000 : ℝ))
      (E := (cell12944 ⟨42, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (1652552592187 / 2000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (277825977149 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_43 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (10324218134527 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222611847623 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨43, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (10324218134527 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222611847623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_44 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16511976799321 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444523175451 / 20000000000000 : ℝ))
      (E := (cell12944 ⟨44, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16511976799321 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (444523175451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_45 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82526046341303 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222619845583 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨45, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82526046341303 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222619845583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_46 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16498446416249 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222623868523 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨46, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16498446416249 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222623868523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_47 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (8245844118751 / 10000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222627885161 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨47, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (8245844118751 / 10000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222627885161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_48 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82424673631323 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555657973309 / 25000000000000 : ℝ))
      (E := (cell12944 ⟨48, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82424673631323 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (555657973309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_49 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (20597732346013 / 25000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222635890273 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨49, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (20597732346013 / 25000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222635890273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_50 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (10294651052151 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222639932589 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨50, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (10294651052151 / 12500000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222639932589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_51 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82323510702447 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (22226438993 / 1000000000000 : ℝ))
      (E := (cell12944 ⟨51, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82323510702447 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (22226438993 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_52 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16457967242313 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (138915494083 / 6250000000000 : ℝ))
      (E := (cell12944 ⟨52, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16457967242313 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (138915494083 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_53 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82256184916497 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222651947427 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨53, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82256184916497 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222651947427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_54 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (41111278394661 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222655963039 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨54, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (41111278394661 / 50000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222655963039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_55 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16437790360451 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222659948429 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨55, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16437790360451 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222659948429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_56 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82155369927651 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222663958797 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨56, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82155369927651 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222663958797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_57 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82121811138001 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222667990067 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨57, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82121811138001 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222667990067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_58 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (16417655081187 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222671978757 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨58, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (16417655081187 / 20000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222671978757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12944_59 : CellCertificate 12944 (109999668206723 / 1250000000000000 : ℝ) (811352693183803 / 500000000000000000 : ℝ) (327631723160149 / 10000000000000000 : ℝ)
    (cell12944 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · norm_num [cell12944]
  · have h := gap_lower (n := 12944) (a := (82054762704217 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222675979523 / 100000000000000 : ℝ))
      (E := (cell12944 ⟨59, by decide⟩).energy) (xi := (327631723160149 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12944 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12944]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12944])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12944) (a := (82054762704217 / 100000000000000 : ℝ)) (b := (159095802227 / 100000000000000 : ℝ)) (q := (2222675979523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12944])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12944]

theorem cert12945_40 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82695466689207 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555621061779 / 25000000000000 : ℝ))
      (E := (cell12945 ⟨40, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82695466689207 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555621061779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_41 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82661535454719 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222488223173 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨41, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82661535454719 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222488223173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_42 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41313813866109 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222492260471 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨42, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41313813866109 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222492260471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_43 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82593743492197 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555624060053 / 25000000000000 : ℝ))
      (E := (cell12945 ⟨43, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82593743492197 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555624060053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_44 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (5159992669081 / 6250000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222500278651 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨44, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (5159992669081 / 6250000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222500278651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_45 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (41263022671151 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222504256463 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨45, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (41263022671151 / 50000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222504256463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_46 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82492231374149 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111254144783 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨46, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82492231374149 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111254144783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_47 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82458440771919 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (222251225811 / 10000000000000 : ℝ))
      (E := (cell12945 ⟨47, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82458440771919 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (222251225811 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_48 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (16484934701367 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (27781453471 / 1250000000000 : ℝ))
      (E := (cell12945 ⟨48, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (16484934701367 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (27781453471 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_49 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82390929550269 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (444504057377 / 20000000000000 : ℝ))
      (E := (cell12945 ⟨49, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82390929550269 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (444504057377 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_50 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82357208873731 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222524283041 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨50, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82357208873731 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222524283041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_51 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82323511448877 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (88901132891 / 4000000000000 : ℝ))
      (E := (cell12945 ⟨51, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82323511448877 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (88901132891 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_52 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (5143114827969 / 6250000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (69454135703 / 3125000000000 : ℝ))
      (E := (cell12945 ⟨52, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (5143114827969 / 6250000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (69454135703 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_53 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82256186241549 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111268170193 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨53, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82256186241549 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111268170193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_54 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (8222255840309 / 10000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111270185757 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨54, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (8222255840309 / 10000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111270185757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_55 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (10273619213043 / 12500000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (222254437309 / 10000000000000 : ℝ))
      (E := (cell12945 ⟨55, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (10273619213043 / 12500000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (222254437309 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_56 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (16431074423533 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222548341173 / 100000000000000 : ℝ))
      (E := (cell12945 ⟨56, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (16431074423533 / 20000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (2222548341173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_57 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82121813615547 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555638097487 / 25000000000000 : ℝ))
      (E := (cell12945 ⟨57, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82121813615547 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (555638097487 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_58 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82088278170619 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111278198407 / 50000000000000 : ℝ))
      (E := (cell12945 ⟨58, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82088278170619 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (1111278198407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12945_59 : CellCertificate 12945 (175994082497833 / 2000000000000000 : ℝ) (1622579992097857 / 1000000000000000000 : ℝ) (163802909856373 / 5000000000000000 : ℝ)
    (cell12945 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · norm_num [cell12945]
  · have h := gap_lower (n := 12945) (a := (82054765755647 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (88902416657 / 4000000000000 : ℝ))
      (E := (cell12945 ⟨59, by decide⟩).energy) (xi := (163802909856373 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12945 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12945]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12945])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12945) (a := (82054765755647 / 100000000000000 : ℝ)) (b := (9942710493 / 6250000000000 : ℝ)) (q := (88902416657 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12945])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12945]

theorem cert12946_40 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (82695464225447 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (222236867317 / 10000000000000 : ℝ))
      (E := (cell12946 ⟨40, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (82695464225447 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (222236867317 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_41 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41330766642423 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555593164013 / 25000000000000 : ℝ))
      (E := (cell12946 ⟨41, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41330766642423 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555593164013 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_42 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (20656906463957 / 25000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222376642039 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨42, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (20656906463957 / 25000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222376642039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_43 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (16518748381777 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (138898793049 / 6250000000000 : ℝ))
      (E := (cell12946 ⟨43, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (16518748381777 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (138898793049 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_44 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (82559881414659 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (88895387089 / 4000000000000 : ℝ))
      (E := (cell12946 ⟨44, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (82559881414659 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (88895387089 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_45 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41263022171969 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222388664557 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨45, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41263022171969 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222388664557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_46 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (10311528833457 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222392707859 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨46, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (10311528833457 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222392707859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_47 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (16491688071379 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222396687279 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨47, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (16491688071379 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222396687279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_48 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41212336691441 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222400718399 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨48, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41212336691441 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222400718399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_49 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (16478185943397 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222404739833 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨49, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (16478185943397 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222404739833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_50 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41178604665359 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555602187223 / 25000000000000 : ℝ))
      (E := (cell12946 ⟨50, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41178604665359 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (555602187223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_51 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (10290439024467 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222412742677 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨51, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (10290439024467 / 12500000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222412742677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_52 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41144919141919 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222416777127 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨52, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41144919141919 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222416777127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_53 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41128093783481 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222420789917 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨53, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41128093783481 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222420789917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_54 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (16444512003437 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (27780309719 / 1250000000000 : ℝ))
      (E := (cell12946 ⟨54, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (16444512003437 / 20000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (27780309719 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_55 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (3287558224269 / 4000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222428795319 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨55, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (3287558224269 / 4000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222428795319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_56 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (41077687153969 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444486556059 / 20000000000000 : ℝ))
      (E := (cell12946 ⟨56, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (41077687153969 / 50000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444486556059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_57 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (82121816093317 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (1111218393733 / 50000000000000 : ℝ))
      (E := (cell12946 ⟨57, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (82121816093317 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (1111218393733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_58 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (82088280935493 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222440812543 / 100000000000000 : ℝ))
      (E := (cell12946 ⟨58, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (82088280935493 / 100000000000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (2222440812543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12946_59 : CellCertificate 12946 (175988696662423 / 2000000000000000 : ℝ) (1622454617206249 / 1000000000000000000 : ℝ) (327579920399837 / 10000000000000000 : ℝ)
    (cell12946 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · norm_num [cell12946]
  · have h := gap_lower (n := 12946) (a := (1282105762613 / 1562500000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444488970207 / 20000000000000 : ℝ))
      (E := (cell12946 ⟨59, by decide⟩).energy) (xi := (327579920399837 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12946 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12946]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12946])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12946) (a := (1282105762613 / 1562500000000 : ℝ)) (b := (79535467751 / 50000000000000 : ℝ)) (q := (444488970207 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12946])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12946]

theorem cert12947_40 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82695461762499 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (111112654813 / 5000000000000 : ℝ))
      (E := (cell12947 ⟨40, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82695461762499 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (111112654813 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_41 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (330646124463 / 400000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222257086003 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨41, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (330646124463 / 400000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222257086003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_42 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82627623980179 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (44445222767 / 2000000000000 : ℝ))
      (E := (cell12947 ⟨42, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82627623980179 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (44445222767 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_43 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (2064843508157 / 2500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (4444530269 / 200000000000 : ℝ))
      (E := (cell12947 ⟨43, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (2064843508157 / 2500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (4444530269 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_44 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (41279940062347 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111134565921 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨44, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (41279940062347 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111134565921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_45 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82526043346211 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111136564377 / 50000000000000 : ℝ))
      (E := (cell12947 ⟨45, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82526043346211 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (1111136564377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_46 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (16498445992353 / 20000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222277182313 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨46, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (16498445992353 / 20000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222277182313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_47 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (2061460998561 / 2500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222281172667 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨47, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (2061460998561 / 2500000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222281172667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_48 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82424673259461 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222285156441 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨48, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82424673259461 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222285156441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_49 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82390929884199 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222289190139 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨49, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82390929884199 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222289190139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_50 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82357209788169 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (277786651517 / 12500000000000 : ℝ))
      (E := (cell12947 ⟨50, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82357209788169 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (277786651517 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_51 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (41161756471513 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222297219533 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨51, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (41161756471513 / 50000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222297219533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_52 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82289839320569 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222301209217 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨52, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82289839320569 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222301209217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_53 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (1285252951449 / 1562500000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444461047389 / 20000000000000 : ℝ))
      (E := (cell12947 ⟨53, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (1285252951449 / 1562500000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444461047389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_54 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82222561631607 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222309240157 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨54, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82222561631607 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222309240157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_55 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82188957509399 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444462643023 / 20000000000000 : ℝ))
      (E := (cell12947 ⟨55, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82188957509399 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444462643023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_56 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (8215537649847 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444463455233 / 20000000000000 : ℝ))
      (E := (cell12947 ⟨56, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (8215537649847 / 10000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444463455233 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_57 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82121818571313 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222321241789 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨57, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82121818571313 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222321241789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_58 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (82088283700559 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444465057027 / 20000000000000 : ℝ))
      (E := (cell12947 ⟨58, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (82088283700559 / 100000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (444465057027 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12947_59 : CellCertificate 12947 (439958279060853 / 5000000000000000 : ℝ) (162232926168829 / 100000000000000000 : ℝ) (81888506305091 / 2500000000000000 : ℝ)
    (cell12947 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · norm_num [cell12947]
  · have h := gap_lower (n := 12947) (a := (3282190874359 / 4000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222329283349 / 100000000000000 : ℝ))
      (E := (cell12947 ⟨59, by decide⟩).energy) (xi := (81888506305091 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12947 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12947]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12947])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12947) (a := (3282190874359 / 4000000000000 : ℝ)) (b := (39764626267 / 25000000000000 : ℝ)) (q := (2222329283349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12947])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12947]

theorem cert12948_40 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41347729650181 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222137575157 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨40, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41347729650181 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222137575157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_41 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (8266152894743 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222141571821 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨41, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (8266152894743 / 10000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222141571821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_42 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (10328452763159 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (277768196619 / 12500000000000 : ℝ))
      (E := (cell12948 ⟨42, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (10328452763159 / 12500000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (277768196619 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_43 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82593738744381 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (27776869717 / 1250000000000 : ℝ))
      (E := (cell12948 ⟨43, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82593738744381 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (27776869717 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_44 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82559878835401 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111076821251 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨44, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82559878835401 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111076821251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_45 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82526042349121 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222157649053 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨45, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82526042349121 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222157649053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_46 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82492229256477 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222161654017 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨46, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82492229256477 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222161654017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_47 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82458439528553 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222165655341 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨47, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82458439528553 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222165655341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_48 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41212336568287 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111084825381 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨48, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41212336568287 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111084825381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_49 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82390930051913 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222173637801 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨49, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82390930051913 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222173637801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_50 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (20589302561521 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555544418193 / 25000000000000 : ℝ))
      (E := (cell12948 ⟨50, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (20589302561521 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555544418193 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_51 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (16464702738149 / 20000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222181693817 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨51, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (16464702738149 / 20000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222181693817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_52 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41144920178847 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (69443303057 / 3125000000000 : ℝ))
      (E := (cell12948 ⟨52, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41144920178847 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (69443303057 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_53 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82256190218871 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222189681471 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨53, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82256190218871 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222189681471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_54 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (20555640811589 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111096850163 / 50000000000000 : ℝ))
      (E := (cell12948 ⟨54, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (20555640811589 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (1111096850163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_55 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41094479706183 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (5555494229 / 250000000000 : ℝ))
      (E := (cell12948 ⟨55, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41094479706183 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (5555494229 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_56 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (4107768934463 / 5000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555550427623 / 25000000000000 : ℝ))
      (E := (cell12948 ⟨56, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (4107768934463 / 5000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555550427623 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_57 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (20530455262383 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222205752919 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨57, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (20530455262383 / 25000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222205752919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_58 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (41044143232907 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222209755401 / 100000000000000 : ℝ))
      (E := (cell12948 ⟨58, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (41044143232907 / 50000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (2222209755401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12948_59 : CellCertificate 12948 (87988963691701 / 1000000000000000 : ℝ) (162220392553949 / 100000000000000000 : ℝ) (40941016771659 / 1250000000000000 : ℝ)
    (cell12948 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · norm_num [cell12948]
  · have h := gap_lower (n := 12948) (a := (82054774910873 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555553443147 / 25000000000000 : ℝ))
      (E := (cell12948 ⟨59, by decide⟩).energy) (xi := (40941016771659 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12948 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12948]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12948])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12948) (a := (82054774910873 / 100000000000000 : ℝ)) (b := (79523038293 / 50000000000000 : ℝ)) (q := (555553443147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12948])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12948]

theorem cert12949_40 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (16539091367807 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111011054931 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨40, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (16539091367807 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111011054931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_41 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (41330763389943 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (444405222701 / 20000000000000 : ℝ))
      (E := (cell12949 ⟨41, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (41330763389943 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (444405222701 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_42 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (16525524046221 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222030122297 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨42, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (16525524046221 / 20000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222030122297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_43 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82593737163189 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555508533761 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨43, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82593737163189 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555508533761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_44 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (4127993877339 / 5000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222038091477 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨44, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (4127993877339 / 5000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222038091477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_45 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (20631510338167 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222042107679 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨45, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (20631510338167 / 25000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222042107679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_46 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82492228551791 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555511530743 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨46, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82492228551791 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555511530743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_47 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82458439115233 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222050135301 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨47, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82458439115233 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222050135301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_48 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (4121233650711 / 5000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555513535601 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨48, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (4121233650711 / 5000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555513535601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_49 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (659127441761 / 800000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (11110290709 / 500000000000 : ℝ))
      (E := (cell12949 ⟨49, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (659127441761 / 800000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (11110290709 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_50 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (5147325669029 / 6250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555515547451 / 25000000000000 : ℝ))
      (E := (cell12949 ⟨50, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (5147325669029 / 6250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (555515547451 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_51 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (41161757219447 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222066165527 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨51, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (41161757219447 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222066165527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_52 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (5143115087201 / 6250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (222207018389 / 10000000000000 : ℝ))
      (E := (cell12949 ⟨52, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (5143115087201 / 6250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (222207018389 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_53 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (10282023943171 / 12500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222074182567 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨53, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (10282023943171 / 12500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222074182567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_54 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82222564861431 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222078217127 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨54, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82222564861431 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222078217127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_55 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (41094480657813 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111041112387 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨55, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (41094480657813 / 50000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111041112387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_56 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (82155380880309 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111043100783 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨56, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (82155380880309 / 100000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111043100783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_57 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (10265227940997 / 12500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111045130843 / 50000000000000 : ℝ))
      (E := (cell12949 ⟨57, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (10265227940997 / 12500000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (1111045130843 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_58 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (4104414461563 / 5000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (277761777917 / 12500000000000 : ℝ))
      (E := (cell12949 ⟨58, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (4104414461563 / 5000000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (277761777917 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

theorem cert12949_59 : CellCertificate 12949 (439931359848549 / 5000000000000000 : ℝ) (10137991304721 / 6250000000000000 : ℝ) (163751123628753 / 5000000000000000 : ℝ)
    (cell12949 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · norm_num [cell12949]
  · have h := gap_lower (n := 12949) (a := (5128423622683 / 6250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222098259533 / 100000000000000 : ℝ))
      (E := (cell12949 ⟨59, by decide⟩).energy) (xi := (163751123628753 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12949 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12949]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12949])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12949) (a := (5128423622683 / 6250000000000 : ℝ)) (b := (159033650057 / 100000000000000 : ℝ)) (q := (2222098259533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12949])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12949]

end BstLean.Part268
