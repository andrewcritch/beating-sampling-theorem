import BstLean.Part268CellShard33Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert13175_40 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82692541507543 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274563445883 / 12500000000000 : ℝ))
      (E := (cell13175 ⟨40, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82692541507543 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (274563445883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_41 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82658619163901 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196511582121 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨41, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82658619163901 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196511582121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_42 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82624720320701 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196515568207 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨42, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82624720320701 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196515568207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_43 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (41295422474229 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098259791453 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨43, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (41295422474229 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098259791453 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_44 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (16511398603567 / 20000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196523624791 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨44, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (16511398603567 / 20000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196523624791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_45 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82523164499641 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196527633311 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨45, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82523164499641 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196527633311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_46 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82489359364833 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (34320807273 / 1562500000000 : ℝ))
      (E := (cell13175 ⟨46, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82489359364833 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (34320807273 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_47 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (644184199879 / 781250000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196535660247 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨47, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (644184199879 / 781250000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196535660247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_48 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (3296872765197 / 4000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (109826983713 / 5000000000000 : ℝ))
      (E := (cell13175 ⟨48, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (3296872765197 / 4000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (109826983713 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_49 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82388083972463 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098271852507 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨49, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82388083972463 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098271852507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_50 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82354372083661 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098273874899 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨50, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82354372083661 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098273874899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_51 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82320683435193 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549137936661 / 25000000000000 : ℝ))
      (E := (cell13175 ⟨51, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82320683435193 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549137936661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_52 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82287017998879 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196555751421 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨52, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82287017998879 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196555751421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_53 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (20563343936669 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (137284988743 / 6250000000000 : ℝ))
      (E := (cell13175 ⟨53, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (20563343936669 / 25000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (137284988743 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_54 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (41109878325341 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549140957581 / 25000000000000 : ℝ))
      (E := (cell13175 ⟨54, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (41109878325341 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (549140957581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_55 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (642079380337 / 781250000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196567838043 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨55, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (642079380337 / 781250000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196567838043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_56 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (82152587816413 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098285919541 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨56, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (82152587816413 / 100000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098285919541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_57 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (41059519011513 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196575888459 / 100000000000000 : ℝ))
      (E := (cell13175 ⟨57, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (41059519011513 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (2196575888459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_58 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (10260688909453 / 12500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098289961327 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨58, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (10260688909453 / 12500000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098289961327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13175_59 : CellCertificate 13175 (109234983089769 / 1250000000000000 : ℝ) (1594245139920879 / 1000000000000000000 : ℝ) (321755767267503 / 10000000000000000 : ℝ)
    (cell13175 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · norm_num [cell13175]
  · have h := gap_lower (n := 13175) (a := (41026003773497 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098291968541 / 50000000000000 : ℝ))
      (E := (cell13175 ⟨59, by decide⟩).energy) (xi := (321755767267503 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13175 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13175]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13175])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13175) (a := (41026003773497 / 50000000000000 : ℝ)) (b := (156274406463 / 100000000000000 : ℝ)) (q := (1098291968541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13175])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13175]

theorem cert13176_40 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41346263848641 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196397092437 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨40, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41346263848641 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196397092437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_41 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (20664651339917 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196401105907 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨41, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (20664651339917 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196401105907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_42 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (20656176630623 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549101272613 / 25000000000000 : ℝ))
      (E := (cell13176 ⟨42, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (20656176630623 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549101272613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_43 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (20647707789067 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (274551137957 / 12500000000000 : ℝ))
      (E := (cell13176 ⟨43, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (20647707789067 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (274551137957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_44 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41278489615829 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098206572047 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨44, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41278489615829 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098206572047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_45 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82523150719473 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549104287803 / 25000000000000 : ℝ))
      (E := (cell13176 ⟨45, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82523150719473 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549104287803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_46 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (20622336397667 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098210591009 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨46, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (20622336397667 / 25000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098210591009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_47 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41227781908173 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098212587741 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨47, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41227781908173 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098212587741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_48 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41210902683877 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196429247211 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨48, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41210902683877 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196429247211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_49 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82388070216281 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (274554152221 / 12500000000000 : ℝ))
      (E := (cell13176 ⟨49, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82388070216281 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (274554152221 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_50 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82354358333463 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196437261381 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨50, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82354358333463 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196437261381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_51 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (3292826787639 / 4000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (21964412571 / 1000000000000 : ℝ))
      (E := (cell13176 ⟨51, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (3292826787639 / 4000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (21964412571 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_52 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (16457400852127 / 20000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (34319458123 / 1562500000000 : ℝ))
      (E := (cell13176 ⟨52, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (16457400852127 / 20000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (34319458123 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_53 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82253362014403 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196449328231 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨53, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82253362014403 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196449328231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_54 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (131551588679 / 160000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098226668839 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨54, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (131551588679 / 160000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098226668839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_55 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82186146962789 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196457344457 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨55, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82186146962789 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196457344457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_56 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41076287051011 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196461403767 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨56, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41076287051011 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196461403767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_57 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (41059512157293 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196465393127 / 100000000000000 : ℝ))
      (E := (cell13176 ⟨57, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (41059512157293 / 50000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (2196465393127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_58 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82085497573131 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098234713259 / 50000000000000 : ℝ))
      (E := (cell13176 ⟨58, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82085497573131 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (1098234713259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13176_59 : CellCertificate 13176 (174770765719119 / 2000000000000000 : ℝ) (1594124105435359 / 1000000000000000000 : ℝ) (80432697922471 / 2500000000000000 : ℝ)
    (cell13176 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · norm_num [cell13176]
  · have h := gap_lower (n := 13176) (a := (82051993850443 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549118360047 / 25000000000000 : ℝ))
      (E := (cell13176 ⟨59, by decide⟩).energy) (xi := (80432697922471 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13176 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13176]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13176])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13176) (a := (82051993850443 / 100000000000000 : ℝ)) (b := (19532801371 / 12500000000000 : ℝ)) (q := (549118360047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13176])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13176]

theorem cert13177_40 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (516828211807 / 625000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549071653411 / 25000000000000 : ℝ))
      (E := (cell13177 ⟨40, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (516828211807 / 625000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549071653411 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_41 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82658591557533 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196290625529 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨41, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82658591557533 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196290625529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_42 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82624692726379 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (17570357339 / 800000000000 : ℝ))
      (E := (cell13177 ⟨42, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82624692726379 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (17570357339 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_43 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82590817366173 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549074669777 / 25000000000000 : ℝ))
      (E := (cell13177 ⟨43, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82590817366173 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549074669777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_44 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (10319620680947 / 12500000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196302718121 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨44, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (10319620680947 / 12500000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196302718121 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_45 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82523136941399 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196306723861 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨45, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82523136941399 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196306723861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_46 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82489331818597 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439262150667 / 20000000000000 : ℝ))
      (E := (cell13177 ⟨46, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82489331818597 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439262150667 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_47 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82455550050273 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439262949103 / 20000000000000 : ℝ))
      (E := (cell13177 ⟨47, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82455550050273 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (439262949103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_48 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (41210895803837 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (68634961157 / 3125000000000 : ℝ))
      (E := (cell13177 ⟨48, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (41210895803837 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (68634961157 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_49 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82388056462189 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196322785367 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨49, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82388056462189 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196322785367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_50 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (16470868917071 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196326827833 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨50, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (16470868917071 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196326827833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_51 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (41160327974423 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196330822451 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨51, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (41160327974423 / 50000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196330822451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_52 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (257146845389 / 312500000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098167412547 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨52, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (257146845389 / 312500000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098167412547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_53 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82253348284217 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196338891517 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨53, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82253348284217 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196338891517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_54 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82219729200153 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098171450001 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨54, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82219729200153 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098171450001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_55 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82186133244527 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098173452931 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨55, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82186133244527 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098173452931 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_56 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (16430512077943 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196350905133 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨56, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (16430512077943 / 20000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196350905133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_57 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82119010608229 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549088738209 / 25000000000000 : ℝ))
      (E := (cell13177 ⟨57, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82119010608229 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (549088738209 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_58 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (1026068548409 / 1250000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098179492723 / 50000000000000 : ℝ))
      (E := (cell13177 ⟨58, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (1026068548409 / 1250000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (1098179492723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13177_59 : CellCertificate 13177 (873827796253663 / 10000000000000000 : ℝ) (797001544663113 / 500000000000000000 : ℝ) (321705820013891 / 10000000000000000 : ℝ)
    (cell13177 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · norm_num [cell13177]
  · have h := gap_lower (n := 13177) (a := (82051980155973 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196362998383 / 100000000000000 : ℝ))
      (E := (cell13177 ⟨59, by decide⟩).energy) (xi := (321705820013891 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13177 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13177]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13177])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13177) (a := (82051980155973 / 100000000000000 : ℝ)) (b := (156250417321 / 100000000000000 : ℝ)) (q := (2196362998383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13177])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13177]

theorem cert13178_40 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (5168281255191 / 6250000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196176189481 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨40, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (5168281255191 / 6250000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196176189481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_41 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (10332322219687 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196180199803 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨41, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (10332322219687 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196180199803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_42 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20656169733091 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196184240133 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨42, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20656169733091 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196184240133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_43 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (41295401789087 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098094125199 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨43, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (41295401789087 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098094125199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_44 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (82556951665589 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098096114551 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨44, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (82556951665589 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098096114551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_45 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (41261561582709 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (8578891767 / 390625000000 : ℝ))
      (E := (cell13178 ⟨45, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (41261561582709 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (8578891767 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_46 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (41244659024309 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098100130781 / 50000000000000 : ℝ))
      (E := (cell13178 ⟨46, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (41244659024309 / 50000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (1098100130781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_47 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20613884071573 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196204311389 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨47, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20613884071573 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196204311389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_48 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20605444462421 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196208321661 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨48, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20605444462421 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196208321661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_49 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20597010677547 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196212348811 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨49, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20597010677547 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196212348811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_50 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (10294291354917 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (219621639013 / 10000000000000 : ℝ))
      (E := (cell13178 ⟨50, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (10294291354917 / 12500000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (219621639013 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_51 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (16464128441761 / 20000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196220383647 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨51, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (16464128441761 / 20000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196220383647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_52 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20571744197603 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (549056096309 / 25000000000000 : ℝ))
      (E := (cell13178 ⟨52, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20571744197603 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (549056096309 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_53 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (82253334556117 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196228450651 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨53, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (82253334556117 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196228450651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_54 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (82219715478017 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196232458173 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨54, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (82219715478017 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196232458173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_55 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (1643722390567 / 2000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196236463117 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨55, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (1643722390567 / 2000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196236463117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_56 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (20538136669873 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196240461517 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨56, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (20538136669873 / 25000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196240461517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_57 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (16423799380791 / 20000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439248901679 / 20000000000000 : ℝ))
      (E := (cell13178 ⟨57, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (16423799380791 / 20000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (439248901679 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_58 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (82085470174391 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196248540227 / 100000000000000 : ℝ))
      (E := (cell13178 ⟨58, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (82085470174391 / 100000000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (2196248540227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13178_59 : CellCertificate 13178 (218450441922873 / 2500000000000000 : ℝ) (99617630724331 / 62500000000000000 : ℝ) (160840426119281 / 5000000000000000 : ℝ)
    (cell13178 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · norm_num [cell13178]
  · have h := gap_lower (n := 13178) (a := (2564123951987 / 3125000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (219625255243 / 10000000000000 : ℝ))
      (E := (cell13178 ⟨59, by decide⟩).energy) (xi := (160840426119281 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13178 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13178]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13178])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13178) (a := (2564123951987 / 3125000000000 : ℝ)) (b := (156238425521 / 100000000000000 : ℝ)) (q := (219625255243 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13178])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13178]

theorem cert13179_40 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (8269248627909 / 10000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1098032880577 / 50000000000000 : ℝ))
      (E := (cell13179 ⟨40, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (8269248627909 / 10000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (1098032880577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_41 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (16531712791911 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196069769917 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨41, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (16531712791911 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196069769917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_42 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (20656166285111 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (549018452183 / 25000000000000 : ℝ))
      (E := (cell13179 ⟨42, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (20656166285111 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (549018452183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_43 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (8259078979227 / 10000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (274509727191 / 12500000000000 : ℝ))
      (E := (cell13179 ⟨43, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (8259078979227 / 10000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (274509727191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_44 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (16511387577139 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196081853697 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨44, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (16511387577139 / 20000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196081853697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_45 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82523109391531 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (549021464171 / 25000000000000 : ℝ))
      (E := (cell13179 ⟨45, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82523109391531 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (549021464171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_46 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (20622326070183 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196089883497 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨46, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (20622326070183 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196089883497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_47 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41227761262201 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196093873107 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨47, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41227761262201 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196093873107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_48 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41210882046893 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196097882141 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨48, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41210882046893 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196097882141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_49 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (20597007240069 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196101908099 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨49, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (20597007240069 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196101908099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_50 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41177158547703 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (137256621767 / 6250000000000 : ℝ))
      (E := (cell13179 ⟨50, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41177158547703 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (137256621767 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_51 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82320628470851 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196109940691 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨51, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82320628470851 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196109940691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_52 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82286963058431 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196114000299 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨52, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82286963058431 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196114000299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_53 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82253320830103 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196118005633 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨53, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82253320830103 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196118005633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_54 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (41109850878983 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (68628812881 / 3125000000000 : ℝ))
      (E := (cell13179 ⟨54, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (41109850878983 / 50000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (68628812881 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_55 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82186105814257 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (439225215073 / 20000000000000 : ℝ))
      (E := (cell13179 ⟨55, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82186105814257 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (439225215073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_56 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (10269066621419 / 12500000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (54903251823 / 2500000000000 : ℝ))
      (E := (cell13179 ⟨56, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (10269066621419 / 12500000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (54903251823 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_57 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (20529745800441 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196134118997 / 100000000000000 : ℝ))
      (E := (cell13179 ⟨57, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (20529745800441 / 25000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (2196134118997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_58 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (82085456478143 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (109806904543 / 5000000000000 : ℝ))
      (E := (cell13179 ⟨58, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (82085456478143 / 100000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (109806904543 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13179_59 : CellCertificate 13179 (43688787145411 / 500000000000000 : ℝ) (796880556110193 / 500000000000000000 : ℝ) (40206986045367 / 1250000000000000 : ℝ)
    (cell13179 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · norm_num [cell13179]
  · have h := gap_lower (n := 13179) (a := (3282078110931 / 4000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (219614216157 / 10000000000000 : ℝ))
      (E := (cell13179 ⟨59, by decide⟩).energy) (xi := (40206986045367 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13179 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13179]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13179])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13179) (a := (3282078110931 / 4000000000000 : ℝ)) (b := (9764152223 / 6250000000000 : ℝ)) (q := (219614216157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13179])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13179]

theorem cert13180_40 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82692472477221 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097977664333 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨40, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82692472477221 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097977664333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_41 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82658550163711 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (439191878937 / 20000000000000 : ℝ))
      (E := (cell13180 ⟨41, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82658550163711 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (439191878937 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_42 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82624651350619 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195963373171 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨42, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82624651350619 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195963373171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_43 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (4129538800423 / 5000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195967439363 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨43, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (4129538800423 / 5000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195967439363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_44 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (10319615513487 / 12500000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097985707623 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨44, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (10319615513487 / 12500000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097985707623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_45 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (10315386952467 / 12500000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (274496934471 / 12500000000000 : ℝ))
      (E := (cell13180 ⟨45, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (10315386952467 / 12500000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (274496934471 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_46 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41244645257469 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097989721171 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨46, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41244645257469 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097989721171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_47 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82455508764603 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097991744813 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨47, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82455508764603 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1097991744813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_48 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82421750339977 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195987497447 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨48, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82421750339977 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195987497447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_49 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82388015212453 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195991522237 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨49, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82388015212453 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195991522237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_50 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (20588575838391 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195995561289 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨50, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (20588575838391 / 25000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2195995561289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_51 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (16464122946997 / 20000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (274499944079 / 12500000000000 : ℝ))
      (E := (cell13180 ⟨51, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (16464122946997 / 20000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (274499944079 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_52 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (10285868666067 / 12500000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (549000902803 / 25000000000000 : ℝ))
      (E := (cell13180 ⟨52, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (10285868666067 / 12500000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (549000902803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_53 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (3290132284247 / 4000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2196007615561 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨53, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (3290132284247 / 4000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2196007615561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_54 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82219688039999 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (34312681581 / 1562500000000 : ℝ))
      (E := (cell13180 ⟨54, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82219688039999 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (34312681581 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_55 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (82186092102247 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2196015624321 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨55, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (82186092102247 / 100000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2196015624321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_56 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (16430503853059 / 20000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1098009840087 / 50000000000000 : ℝ))
      (E := (cell13180 ⟨56, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (16430503853059 / 20000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (1098009840087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_57 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41059484750827 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2196023666261 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨57, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41059484750827 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2196023666261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_58 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (10260680347997 / 12500000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2196027696561 / 100000000000000 : ℝ))
      (E := (cell13180 ⟨58, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (10260680347997 / 12500000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (2196027696561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13180_59 : CellCertificate 13180 (436874860951491 / 5000000000000000 : ℝ) (1593640151215313 / 1000000000000000000 : ℝ) (80407732096513 / 2500000000000000 : ℝ)
    (cell13180 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · norm_num [cell13180]
  · have h := gap_lower (n := 13180) (a := (41025969542523 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (87841268293 / 4000000000000 : ℝ))
      (E := (cell13180 ⟨59, by decide⟩).energy) (xi := (80407732096513 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13180 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13180]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13180])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13180) (a := (41025969542523 / 50000000000000 : ℝ)) (b := (156214447461 / 100000000000000 : ℝ)) (q := (87841268293 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13180])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13180]

theorem cert13181_40 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82692458677449 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (219584495081 / 10000000000000 : ℝ))
      (E := (cell13181 ⟨40, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82692458677449 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (219584495081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_41 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82658536369963 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195849015293 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨41, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82658536369963 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195849015293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_42 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (8262463756289 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (219585299229 / 10000000000000 : ℝ))
      (E := (cell13181 ⟨42, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (8262463756289 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (219585299229 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_43 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (16518152445349 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195857057039 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨43, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (16518152445349 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195857057039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_44 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82556910332189 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097930515763 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨44, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82556910332189 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097930515763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_45 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41261540925017 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195865090697 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨45, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41261540925017 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195865090697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_46 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (16497855350247 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195869114899 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨46, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (16497855350247 / 20000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195869114899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_47 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41227747503447 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (274484137749 / 12500000000000 : ℝ))
      (E := (cell13181 ⟨47, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41227747503447 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (274484137749 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_48 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41210868294129 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195877108599 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨48, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41210868294129 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195877108599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_49 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82388001466719 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195881132223 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨49, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82388001466719 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195881132223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_50 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82354289613809 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (439177034031 / 20000000000000 : ℝ))
      (E := (cell13181 ⟨50, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82354289613809 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (439177034031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_51 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41160300500603 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097944609737 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨51, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41160300500603 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097944609737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_52 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82286935600727 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097946608987 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨52, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82286935600727 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097946608987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_53 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (20563323346083 / 25000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195897221341 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨53, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (20563323346083 / 25000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195897221341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_54 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82219674324117 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195901226027 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨54, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82219674324117 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195901226027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_55 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82186078392321 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097952643709 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨55, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82186078392321 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097952643709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_56 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (2053812639033 / 2500000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097954641641 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨56, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (2053812639033 / 2500000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097954641641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_57 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (41059477901813 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097956663881 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨57, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (41059477901813 / 50000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097956663881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_58 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (8208542909189 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195917357333 / 100000000000000 : ℝ))
      (E := (cell13181 ⟨58, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (8208542909189 / 10000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (2195917357333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13181_59 : CellCertificate 13181 (174744740934983 / 2000000000000000 : ℝ) (199189901071237 / 125000000000000000 : ℝ) (321605972306947 / 10000000000000000 : ℝ)
    (cell13181 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · norm_num [cell13181]
  · have h := gap_lower (n := 13181) (a := (82051925398897 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097960683707 / 50000000000000 : ℝ))
      (E := (cell13181 ⟨59, by decide⟩).energy) (xi := (321605972306947 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13181 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13181]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13181])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13181) (a := (82051925398897 / 100000000000000 : ℝ)) (b := (156202461199 / 100000000000000 : ℝ)) (q := (1097960683707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13181])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13181]

theorem cert13182_40 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82692444879773 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548933656897 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨40, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82692444879773 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548933656897 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_41 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (8265852257831 / 10000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195738631743 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨41, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (8265852257831 / 10000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195738631743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_42 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (16524924755451 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195742666091 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨42, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (16524924755451 / 20000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195742666091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_43 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82590748447123 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097873335279 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨43, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82590748447123 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097873335279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_44 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (5159806034911 / 6250000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097875351267 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨44, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (5159806034911 / 6250000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097875351267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_45 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82523068082423 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (219575470147 / 10000000000000 : ℝ))
      (E := (cell13182 ⟨45, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82523068082423 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (219575470147 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_46 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82489262989623 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (137234920273 / 6250000000000 : ℝ))
      (E := (cell13182 ⟨46, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82489262989623 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (137234920273 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_47 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (3298219250051 / 4000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (54894069229 / 2500000000000 : ℝ))
      (E := (cell13182 ⟨47, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (3298219250051 / 4000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (54894069229 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_48 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20605430709657 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195766774579 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨48, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20605430709657 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195766774579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_49 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (1287312308173 / 1562500000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195770797061 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨49, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (1287312308173 / 1562500000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195770797061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_50 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (41177137938071 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274471854237 / 12500000000000 : ℝ))
      (E := (cell13182 ⟨50, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (41177137938071 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274471854237 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_51 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82320587269513 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097889411557 / 50000000000000 : ℝ))
      (E := (cell13182 ⟨51, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82320587269513 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (1097889411557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_52 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20571730468751 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (109789143983 / 5000000000000 : ℝ))
      (E := (cell13182 ⟨52, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20571730468751 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (109789143983 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_53 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82253279664573 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (219578688207 / 10000000000000 : ℝ))
      (E := (cell13182 ⟨53, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82253279664573 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (219578688207 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_54 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (41109830305159 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548947721461 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨54, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (41109830305159 / 50000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548947721461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_55 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82186064684477 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274474360903 / 12500000000000 : ℝ))
      (E := (cell13182 ⟨55, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82186064684477 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274474360903 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_56 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82152491859427 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548949735353 / 25000000000000 : ℝ))
      (E := (cell13182 ⟨56, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82152491859427 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (548949735353 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_57 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (82118942107679 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195802985117 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨57, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (82118942107679 / 100000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195802985117 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_58 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20521353850471 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274475869343 / 12500000000000 : ℝ))
      (E := (cell13182 ⟨58, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20521353850471 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (274475869343 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13182_59 : CellCertificate 13182 (436848845611579 / 5000000000000000 : ℝ) (318679656855991 / 200000000000000000 : ℝ) (160790510062331 / 5000000000000000 : ℝ)
    (cell13182 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · norm_num [cell13182]
  · have h := gap_lower (n := 13182) (a := (20512977928707 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195811023357 / 100000000000000 : ℝ))
      (E := (cell13182 ⟨59, by decide⟩).energy) (xi := (160790510062331 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13182 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13182]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13182])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13182) (a := (20512977928707 / 25000000000000 : ℝ)) (b := (156190476783 / 100000000000000 : ℝ)) (q := (2195811023357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13182])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13182]

theorem cert13183_40 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41346215542097 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439124860041 / 20000000000000 : ℝ))
      (E := (cell13183 ⟨40, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41346215542097 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439124860041 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_41 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (5166156799297 / 6250000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195628302851 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨41, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (5166156799297 / 6250000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195628302851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_42 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41312304996857 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439126467147 / 20000000000000 : ℝ))
      (E := (cell13183 ⟨42, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41312304996857 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439126467147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_43 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41295367334797 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (68613635587 / 3125000000000 : ℝ))
      (E := (cell13183 ⟨43, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41295367334797 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (68613635587 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_44 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41278441393527 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195640369389 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨44, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41278441393527 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195640369389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_45 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (10315381789613 / 12500000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097822183499 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨45, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (10315381789613 / 12500000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097822183499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_46 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (82489249230101 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195648388617 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨46, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (82489249230101 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195648388617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_47 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41227733748873 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (87826097287 / 4000000000000 : ℝ))
      (E := (cell13183 ⟨47, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41227733748873 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (87826097287 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_48 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (82421709091087 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097828218203 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨48, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (82421709091087 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097828218203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_49 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41193986990757 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195660457747 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨49, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41193986990757 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195660457747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_50 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41177131070281 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097832246743 / 50000000000000 : ℝ))
      (E := (cell13183 ⟨50, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41177131070281 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (1097832246743 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_51 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41160286769953 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439133696331 / 20000000000000 : ℝ))
      (E := (cell13183 ⟨51, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41160286769953 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (439133696331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_52 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (16457381630273 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195672537199 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨52, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (16457381630273 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195672537199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_53 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41126632973449 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195676538651 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨53, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41126632973449 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195676538651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_54 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (41109823449301 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195680541513 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨54, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (41109823449301 / 50000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195680541513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_55 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (20546512744679 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548921150293 / 25000000000000 : ℝ))
      (E := (cell13183 ⟨55, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (20546512744679 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548921150293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_56 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (16430495631923 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548922148849 / 25000000000000 : ℝ))
      (E := (cell13183 ⟨56, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (16430495631923 / 20000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (548922148849 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_57 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (20529732103453 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (274461579791 / 12500000000000 : ℝ))
      (E := (cell13183 ⟨57, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (20529732103453 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (274461579791 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_58 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (82085401713957 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195696666443 / 100000000000000 : ℝ))
      (E := (cell13183 ⟨58, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (82085401713957 / 100000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (2195696666443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13183_59 : CellCertificate 13183 (873671681546847 / 10000000000000000 : ℝ) (1593277378341313 / 1000000000000000000 : ℝ) (321556071838237 / 10000000000000000 : ℝ)
    (cell13183 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · norm_num [cell13183]
  · have h := gap_lower (n := 13183) (a := (20512974508209 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (54892516879 / 2500000000000 : ℝ))
      (E := (cell13183 ⟨59, by decide⟩).energy) (xi := (321556071838237 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13183 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13183]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13183])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13183) (a := (20512974508209 / 25000000000000 : ℝ)) (b := (39044623553 / 25000000000000 : ℝ)) (q := (54892516879 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13183])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13183]

theorem cert13184_40 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82692417290709 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195513968667 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨40, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82692417290709 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195513968667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_41 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82658495001289 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195517969803 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨41, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82658495001289 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195517969803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_42 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82624596212267 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195522001223 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨42, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82624596212267 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195522001223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_43 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (41295360447079 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439105200571 / 20000000000000 : ℝ))
      (E := (cell13184 ⟨43, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (41295360447079 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439105200571 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_44 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (10319608627203 / 12500000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195530032089 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨44, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (10319608627203 / 12500000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195530032089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_45 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (20630760138369 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195534028373 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨45, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (20630760138369 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195534028373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_46 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82489235472669 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195538048713 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨46, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82489235472669 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195538048713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_47 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (41227726873153 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097771045519 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨47, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (41227726873153 / 50000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097771045519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_48 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82421695345633 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195546094083 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨48, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82421695345633 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195546094083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_49 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82387960242043 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195550114283 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨49, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82387960242043 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195550114283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_50 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82354248407067 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195554148929 / 100000000000000 : ℝ))
      (E := (cell13184 ⟨50, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82354248407067 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (2195554148929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_51 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (2572517494137 / 3125000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (21955581951 / 1000000000000 : ℝ))
      (E := (cell13184 ⟨51, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (2572517494137 / 3125000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (21955581951 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_52 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82286894429811 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (219556219059 / 10000000000000 : ℝ))
      (E := (cell13184 ⟨52, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82286894429811 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (219556219059 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_53 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82253252231307 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439113238217 / 20000000000000 : ℝ))
      (E := (cell13184 ⟨53, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82253252231307 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439113238217 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_54 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82219633188969 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097785126079 / 50000000000000 : ℝ))
      (E := (cell13184 ⟨54, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82219633188969 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (1097785126079 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_55 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (20546509318759 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (274446781479 / 12500000000000 : ℝ))
      (E := (cell13184 ⟨55, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (20546509318759 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (274446781479 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_56 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (20538116115471 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439115660881 / 20000000000000 : ℝ))
      (E := (cell13184 ⟨56, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (20538116115471 / 25000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439115660881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_57 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (3284756588881 / 4000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439116457479 / 20000000000000 : ℝ))
      (E := (cell13184 ⟨57, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (3284756588881 / 4000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439116457479 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_58 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82085388028109 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439117262957 / 20000000000000 : ℝ))
      (E := (cell13184 ⟨58, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82085388028109 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (439117262957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13184_59 : CellCertificate 13184 (2730142736391 / 31250000000000 : ℝ) (49786140335931 / 31250000000000000 : ℝ) (321531127446711 / 10000000000000000 : ℝ)
    (cell13184 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · norm_num [cell13184]
  · have h := gap_lower (n := 13184) (a := (82051884352923 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (109779516141 / 5000000000000 : ℝ))
      (E := (cell13184 ⟨59, by decide⟩).energy) (xi := (321531127446711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13184 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13184]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13184])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13184) (a := (82051884352923 / 100000000000000 : ℝ)) (b := (31233302697 / 20000000000000 : ℝ)) (q := (109779516141 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13184])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13184]

theorem cert13185_40 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (2067310087483 / 2500000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195403632971 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨40, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (2067310087483 / 2500000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195403632971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_41 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82658481215919 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439081538283 / 20000000000000 : ℝ))
      (E := (cell13185 ⟨41, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82658481215919 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439081538283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_42 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82624582432913 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548852930349 / 25000000000000 : ℝ))
      (E := (cell13185 ⟨42, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82624582432913 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548852930349 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_43 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41295353560407 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439083144327 / 20000000000000 : ℝ))
      (E := (cell13185 ⟨43, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41295353560407 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (439083144327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_44 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41278427625143 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097709874761 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨44, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41278427625143 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097709874761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_45 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41261513396069 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097711872253 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨45, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41261513396069 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097711872253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_46 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82489221717327 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195427763591 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨46, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82489221717327 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195427763591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_47 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41227719998477 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195431804709 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨47, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41227719998477 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195431804709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_48 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (20605420400567 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195435806591 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨48, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (20605420400567 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195435806591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_49 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41193973252329 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (87817593027 / 4000000000000 : ℝ))
      (E := (cell13185 ⟨49, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41193973252329 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (87817593027 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_50 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82354234675659 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (8781775437 / 400000000000 : ℝ))
      (E := (cell13185 ⟨50, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82354234675659 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (8781775437 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_51 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (20580136521737 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548861976099 / 25000000000000 : ℝ))
      (E := (cell13185 ⟨51, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (20580136521737 / 25000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548861976099 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_52 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82286880710341 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548862974727 / 25000000000000 : ℝ))
      (E := (cell13185 ⟨52, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82286880710341 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (548862974727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_53 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82253238517799 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195455898471 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨53, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82253238517799 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195455898471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_54 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41109809740709 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195459958659 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨54, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41109809740709 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195459958659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_55 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (41093011786719 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195463957491 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨55, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (41093011786719 / 50000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195463957491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_56 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82152450766233 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195467950103 / 100000000000000 : ℝ))
      (E := (cell13185 ⟨56, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82152450766233 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (2195467950103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_57 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (82118901032317 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097735995757 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨57, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (82118901032317 / 100000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097735995757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_58 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (4104268717217 / 5000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (10977380091 / 500000000000 : ℝ))
      (E := (cell13185 ⟨58, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (4104268717217 / 5000000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (10977380091 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13185_59 : CellCertificate 13185 (174723934703423 / 2000000000000000 : ℝ) (49782363171913 / 31250000000000000 : ℝ) (160753093474563 / 5000000000000000 : ℝ)
    (cell13185 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · norm_num [cell13185]
  · have h := gap_lower (n := 13185) (a := (5128241917193 / 6250000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097740012789 / 50000000000000 : ℝ))
      (E := (cell13185 ⟨59, by decide⟩).energy) (xi := (160753093474563 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13185 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13185]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13185])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13185) (a := (5128241917193 / 6250000000000 : ℝ)) (b := (78077267301 / 50000000000000 : ℝ)) (q := (1097740012789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13185])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13185]

theorem cert13186_40 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (3307695588401 / 4000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195293351913 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨40, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (3307695588401 / 4000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195293351913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_41 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (20664616858161 / 25000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195297408873 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨41, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (20664616858161 / 25000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195297408873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_42 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82624568655651 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (274412679677 / 12500000000000 : ℝ))
      (E := (cell13186 ⟨42, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82624568655651 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (274412679677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_43 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (41295346674781 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195305436263 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨43, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (41295346674781 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195305436263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_44 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (41278420742519 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548827365701 / 25000000000000 : ℝ))
      (E := (cell13186 ⟨44, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (41278420742519 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548827365701 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_45 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (8252301303289 / 10000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (274414182061 / 12500000000000 : ℝ))
      (E := (cell13186 ⟨45, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (8252301303289 / 10000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (274414182061 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_46 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82489207964073 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (27441468429 / 1250000000000 : ℝ))
      (E := (cell13186 ⟨46, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82489207964073 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (27441468429 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_47 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82455426249691 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195321514229 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨47, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82455426249691 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195321514229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_48 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82421667860989 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (43906510299 / 2000000000000 : ℝ))
      (E := (cell13186 ⟨48, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82421667860989 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (43906510299 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_49 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (1029849159617 / 1250000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097664766459 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨49, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (1029849159617 / 1250000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097664766459 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_50 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (2573569404573 / 3125000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (87813342617 / 4000000000000 : ℝ))
      (E := (cell13186 ⟨50, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (2573569404573 / 3125000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (87813342617 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_51 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (16464106472719 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548834402387 / 25000000000000 : ℝ))
      (E := (cell13186 ⟨51, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (16464106472719 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (548834402387 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_52 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (16457373398591 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097670801541 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨52, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (16457373398591 / 20000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097670801541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_53 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82253224806373 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195345660813 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨53, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82253224806373 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195345660813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_54 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82219605775949 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (274418707627 / 12500000000000 : ℝ))
      (E := (cell13186 ⟨54, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82219605775949 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (274418707627 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_55 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (32103910107 / 39062500000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (219535365901 / 10000000000000 : ℝ))
      (E := (cell13186 ⟨55, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (32103910107 / 39062500000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (219535365901 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_56 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (41076218536331 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195357709997 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨56, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (41076218536331 / 50000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195357709997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_57 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (5132430459043 / 6250000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195361691491 / 100000000000000 : ℝ))
      (E := (cell13186 ⟨57, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (5132430459043 / 6250000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (2195361691491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_58 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82085360662649 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (87814628699 / 4000000000000 : ℝ))
      (E := (cell13186 ⟨58, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82085360662649 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (87814628699 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13186_59 : CellCertificate 13186 (87359367516197 / 1000000000000000 : ℝ) (1592914770591411 / 1000000000000000000 : ℝ) (160740625172261 / 5000000000000000 : ℝ)
    (cell13186 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · norm_num [cell13186]
  · have h := gap_lower (n := 13186) (a := (82051856999329 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097684891719 / 50000000000000 : ℝ))
      (E := (cell13186 ⟨59, by decide⟩).energy) (xi := (160740625172261 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13186 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13186]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13186])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13186) (a := (82051856999329 / 100000000000000 : ℝ)) (b := (78071278781 / 50000000000000 : ℝ)) (q := (1097684891719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13186])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13186]

theorem cert13187_40 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (10336546990353 / 12500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195183125493 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨40, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (10336546990353 / 12500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195183125493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_41 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82658453651461 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (133983589 / 6103515625 : ℝ))
      (E := (cell13187 ⟨41, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82658453651461 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (133983589 / 6103515625 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_42 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (41312277440241 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097595574641 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨42, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (41312277440241 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097595574641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_43 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82590679580401 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195195205601 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨43, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82590679580401 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195195205601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_44 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (2063920693047 / 2500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439039834387 / 20000000000000 : ℝ))
      (E := (cell13187 ⟨44, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (2063920693047 / 2500000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (439039834387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_45 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82522999275731 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195203223229 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨45, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82522999275731 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195203223229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_46 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (20622298553227 / 25000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (274400904979 / 12500000000000 : ℝ))
      (E := (cell13187 ⟨46, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (20622298553227 / 25000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (274400904979 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_47 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (16491082500903 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097605639279 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨47, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (16491082500903 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097605639279 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_48 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82421654121797 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097607639071 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨48, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82421654121797 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097607639071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_49 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82387919036147 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195219295019 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨49, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82387919036147 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195219295019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_50 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (41177103609549 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (27440291581 / 1250000000000 : ℝ))
      (E := (cell13187 ⟨50, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (41177103609549 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (27440291581 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_51 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82320518642327 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195227310553 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨51, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82320518642327 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195227310553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_52 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82286853277651 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097615681093 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨52, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82286853277651 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097615681093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_53 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (8225321109703 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (219523535991 / 10000000000000 : ℝ))
      (E := (cell13187 ⟨53, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (8225321109703 / 10000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (219523535991 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_54 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82219592072561 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (137202463647 / 6250000000000 : ℝ))
      (E := (cell13187 ⟨54, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82219592072561 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (137202463647 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_55 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82185996176483 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (219524341553 / 10000000000000 : ℝ))
      (E := (cell13187 ⟨55, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82185996176483 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (219524341553 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_56 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (82152423381171 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195247465747 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨56, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (82152423381171 / 100000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195247465747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_57 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (41059436829569 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195251446519 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨57, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (41059436829569 / 50000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195251446519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_58 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (16417069396607 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097627735913 / 50000000000000 : ℝ))
      (E := (cell13187 ⟨58, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (16417069396607 / 20000000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (1097627735913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13187_59 : CellCertificate 13187 (34942707223153 / 400000000000000 : ℝ) (1592793938016203 / 1000000000000000000 : ℝ) (321456317631941 / 10000000000000000 : ℝ)
    (cell13187 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · norm_num [cell13187]
  · have h := gap_lower (n := 13187) (a := (5128240207853 / 6250000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195259477917 / 100000000000000 : ℝ))
      (E := (cell13187 ⟨59, by decide⟩).energy) (xi := (321456317631941 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13187 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13187]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13187])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13187) (a := (5128240207853 / 6250000000000 : ℝ)) (b := (78065291183 / 50000000000000 : ℝ)) (q := (2195259477917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13187])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13187]

theorem cert13188_40 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (20673090534429 / 25000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (54876822373 / 2500000000000 : ℝ))
      (E := (cell13188 ⟨40, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (20673090534429 / 25000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (54876822373 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_41 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (8265843987237 / 10000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (439015378029 / 20000000000000 : ℝ))
      (E := (cell13188 ⟨41, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (8265843987237 / 10000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (439015378029 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_42 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (20656135276851 / 25000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195080915837 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨42, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (20656135276851 / 25000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195080915837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_43 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82590665813331 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (87803396477 / 4000000000000 : ℝ))
      (E := (cell13188 ⟨43, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82590665813331 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (87803396477 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_44 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82556813960813 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195088935801 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨44, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82556813960813 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195088935801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_45 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82522985520661 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097546492911 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨45, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82522985520661 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097546492911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_46 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82489180463831 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195097001197 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨46, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82489180463831 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195097001197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_47 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41227699380713 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (109755051937 / 5000000000000 : ℝ))
      (E := (cell13188 ⟨47, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41227699380713 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (109755051937 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_48 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82421640384691 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (548776259297 / 25000000000000 : ℝ))
      (E := (cell13188 ⟨48, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82421640384691 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (548776259297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_49 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (4119395265251 / 5000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097554526487 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨49, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (4119395265251 / 5000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097554526487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_50 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (10294274186743 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (4287330241 / 195312500000 : ℝ))
      (E := (cell13188 ⟨50, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (10294274186743 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (4287330241 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_51 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41160252461571 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097558533233 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨51, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41160252461571 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097558533233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_52 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (8228683956443 / 10000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097560558573 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨52, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (8228683956443 / 10000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097560558573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_53 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (10281649673721 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (439025022793 / 20000000000000 : ℝ))
      (E := (cell13188 ⟨53, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (10281649673721 / 12500000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (439025022793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_54 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41109789185627 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (439025834309 / 20000000000000 : ℝ))
      (E := (cell13188 ⟨54, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41109789185627 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (439025834309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_55 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41092991240563 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195133167909 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨55, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41092991240563 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195133167909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_56 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82152409691759 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195137217359 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨56, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82152409691759 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195137217359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_57 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41059429987833 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (68598162419 / 3125000000000 : ℝ))
      (E := (cell13188 ⟨57, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41059429987833 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (68598162419 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_58 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (82085333305499 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097572611019 / 50000000000000 : ℝ))
      (E := (cell13188 ⟨58, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (82085333305499 / 100000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (1097572611019 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13188_59 : CellCertificate 13188 (873541689766817 / 10000000000000000 : ℝ) (79633656188571 / 50000000000000000 : ℝ) (321431388810423 / 10000000000000000 : ℝ)
    (cell13188 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · norm_num [cell13188]
  · have h := gap_lower (n := 13188) (a := (41025914827021 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195149286739 / 100000000000000 : ℝ))
      (E := (cell13188 ⟨59, by decide⟩).energy) (xi := (321431388810423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13188 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13188]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13188])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13188) (a := (41025914827021 / 50000000000000 : ℝ)) (b := (39029652253 / 25000000000000 : ℝ)) (q := (2195149286739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13188])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13188]

theorem cert13189_40 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82692348354701 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (438992532039 / 20000000000000 : ℝ))
      (E := (cell13189 ⟨40, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82692348354701 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (438992532039 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_41 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (20664606523843 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194966653961 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨41, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (20664606523843 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194966653961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_42 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82624527336417 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194970678241 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨42, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82624527336417 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194970678241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_43 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82590652048351 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194974731827 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨43, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82590652048351 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194974731827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_44 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (16511360040367 / 20000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194978754407 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨44, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (16511360040367 / 20000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194978754407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_45 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82522971767679 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194982744267 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨45, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82522971767679 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194982744267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_46 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41244583358421 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194986758413 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨46, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41244583358421 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2194986758413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_47 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82455385020423 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274373849347 / 12500000000000 : ℝ))
      (E := (cell13189 ⟨47, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82455385020423 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274373849347 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_48 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82421626649671 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274374349011 / 12500000000000 : ℝ))
      (E := (cell13189 ⟨48, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82421626649671 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274374349011 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_49 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82387891575977 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (438999761357 / 20000000000000 : ℝ))
      (E := (cell13189 ⟨49, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82387891575977 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (438999761357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_50 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (41177089885437 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195002836159 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨50, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (41177089885437 / 50000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195002836159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_51 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (2058012280151 / 2500000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195006877287 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨51, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (2058012280151 / 2500000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195006877287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_52 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82286825853291 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (439002173593 / 20000000000000 : ℝ))
      (E := (cell13189 ⟨52, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82286825853291 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (439002173593 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_53 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (20563295921147 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (68594216343 / 3125000000000 : ℝ))
      (E := (cell13189 ⟨53, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (20563295921147 / 25000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (68594216343 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_54 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82219564672027 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195018920599 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨54, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82219564672027 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195018920599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_55 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (10273246098481 / 12500000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (439004595059 / 20000000000000 : ℝ))
      (E := (cell13189 ⟨55, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (10273246098481 / 12500000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (439004595059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_56 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (3286095840177 / 4000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195026964831 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨56, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (3286095840177 / 4000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195026964831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_57 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (320776743337 / 390625000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195031003351 / 100000000000000 : ℝ))
      (E := (cell13189 ⟨57, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (320776743337 / 390625000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (2195031003351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_58 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82085319630039 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (219503502733 / 10000000000000 : ℝ))
      (E := (cell13189 ⟨58, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82085319630039 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (219503502733 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13189_59 : CellCertificate 13189 (873515702725087 / 10000000000000000 : ℝ) (1592552327852891 / 1000000000000000000 : ℝ) (80351615969753 / 2500000000000000 : ℝ)
    (cell13189 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · norm_num [cell13189]
  · have h := gap_lower (n := 13189) (a := (82051815984513 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274379879023 / 12500000000000 : ℝ))
      (E := (cell13189 ⟨59, by decide⟩).energy) (xi := (80351615969753 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13189 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13189]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13189])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13189) (a := (82051815984513 / 100000000000000 : ℝ)) (b := (12488531 / 8000000000 : ℝ)) (q := (274379879023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13189])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13189]

theorem cert13190_40 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82692334573779 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (219485248011 / 10000000000000 : ℝ))
      (E := (cell13190 ⟨40, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82692334573779 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (219485248011 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_41 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41329206160233 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194856472441 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨41, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41329206160233 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194856472441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_42 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82624513567521 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438972099067 / 20000000000000 : ℝ))
      (E := (cell13190 ⟨42, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82624513567521 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438972099067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_43 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (4129531914273 / 5000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548716122179 / 25000000000000 : ℝ))
      (E := (cell13190 ⟨43, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (4129531914273 / 5000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548716122179 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_44 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (16511357288989 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (274358563747 / 12500000000000 : ℝ))
      (E := (cell13190 ⟨44, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (16511357288989 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (274358563747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_45 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41261479008393 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194872557473 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨45, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41261479008393 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194872557473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_46 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82489152971939 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194876570417 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨46, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82489152971939 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194876570417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_47 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82455371281507 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097440302811 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨47, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82455371281507 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097440302811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_48 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82421612916737 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097442300911 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨48, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82421612916737 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097442300911 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_49 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82387877849019 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097444307727 / 50000000000000 : ℝ))
      (E := (cell13190 ⟨49, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82387877849019 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (1097444307727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_50 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (2573567689059 / 3125000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194892643809 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨50, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (2573567689059 / 3125000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194892643809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_51 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (4116023874551 / 5000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438979336793 / 20000000000000 : ℝ))
      (E := (cell13190 ⟨51, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (4116023874551 / 5000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438979336793 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_52 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (41143406072117 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438980134743 / 20000000000000 : ℝ))
      (E := (cell13190 ⟨52, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (41143406072117 / 50000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438980134743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_53 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (5140823123843 / 6250000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438980945569 / 20000000000000 : ℝ))
      (E := (cell13190 ⟨53, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (5140823123843 / 6250000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (438980945569 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_54 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (513872193593 / 625000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194908724633 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨54, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (513872193593 / 625000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194908724633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_55 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (10273244387081 / 12500000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194912778541 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨55, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (10273244387081 / 12500000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194912778541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_56 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82152382319169 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194916767333 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨56, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82152382319169 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194916767333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_57 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (16423766522991 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548730201289 / 25000000000000 : ℝ))
      (E := (cell13190 ⟨57, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (16423766522991 / 20000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548730201289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_58 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (5130331622291 / 6250000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194924828483 / 100000000000000 : ℝ))
      (E := (cell13190 ⟨58, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (5130331622291 / 6250000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (2194924828483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13190_59 : CellCertificate 13190 (218372429863193 / 2500000000000000 : ℝ) (24881742972757 / 15625000000000000 : ℝ) (1285526171347 / 40000000000000 : ℝ)
    (cell13190 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · norm_num [cell13190]
  · have h := gap_lower (n := 13190) (a := (82051802317059 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548732208183 / 25000000000000 : ℝ))
      (E := (cell13190 ⟨59, by decide⟩).energy) (xi := (1285526171347 / 40000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13190 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13190]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13190])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13190) (a := (82051802317059 / 100000000000000 : ℝ)) (b := (156094667831 / 100000000000000 : ℝ)) (q := (548732208183 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13190])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13190]

theorem cert13191_40 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82692320794949 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548685573969 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨40, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82692320794949 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548685573969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_41 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (1653167970953 / 2000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (87789851471 / 4000000000000 : ℝ))
      (E := (cell13191 ⟨41, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (1653167970953 / 2000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (87789851471 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_42 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (20656124950179 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (54868757707 / 2500000000000 : ℝ))
      (E := (cell13191 ⟨42, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (20656124950179 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (54868757707 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_43 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82590624524659 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438950871837 / 20000000000000 : ℝ))
      (E := (cell13191 ⟨43, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82590624524659 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438950871837 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_44 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (2579899146567 / 3125000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194758379173 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨44, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (2579899146567 / 3125000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194758379173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_45 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (4126147213399 / 5000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438952473307 / 20000000000000 : ℝ))
      (E := (cell13191 ⟨45, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (4126147213399 / 5000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (438952473307 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_46 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82489139229123 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548691594569 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨46, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82489139229123 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548691594569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_47 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82455357544677 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548692603081 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨47, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82455357544677 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548692603081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_48 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82421599185887 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097387203707 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨48, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82421599185887 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097387203707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_49 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (5149241507759 / 6250000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194778478987 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨49, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (5149241507759 / 6250000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194778478987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_50 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (10294269041373 / 12500000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194782447319 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨50, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (10294269041373 / 12500000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194782447319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_51 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82320463778083 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097393243251 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨51, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82320463778083 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097393243251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_52 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41143399218629 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194790534401 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨52, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41143399218629 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194790534401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_53 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (20563289070117 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194794528577 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨53, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (20563289070117 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194794528577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_54 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (20554884319953 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548699645913 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨54, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (20554884319953 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548699645913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_55 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (10273242675941 / 12500000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194802577649 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨55, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (10273242675941 / 12500000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194802577649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_56 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (8215236863599 / 10000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (219480662487 / 10000000000000 : ℝ))
      (E := (cell13191 ⟨56, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (8215236863599 / 10000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (219480662487 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_57 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (41059409468857 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097405301413 / 50000000000000 : ℝ))
      (E := (cell13191 ⟨57, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (41059409468857 / 50000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (1097405301413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_58 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (20521323071337 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194814625503 / 100000000000000 : ℝ))
      (E := (cell13191 ⟨58, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (20521323071337 / 25000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (2194814625503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13191_59 : CellCertificate 13191 (436731869974507 / 5000000000000000 : ℝ) (1592310790977921 / 1000000000000000000 : ℝ) (321356625682679 / 10000000000000000 : ℝ)
    (cell13191 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · norm_num [cell13191]
  · have h := gap_lower (n := 13191) (a := (82051788651679 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548704672097 / 25000000000000 : ℝ))
      (E := (cell13191 ⟨59, by decide⟩).energy) (xi := (321356625682679 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13191 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13191]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13191])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13191) (a := (82051788651679 / 100000000000000 : ℝ)) (b := (78041350001 / 50000000000000 : ℝ)) (q := (548704672097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13191])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13191]

theorem cert13192_40 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82692307018211 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194632107491 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨40, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82692307018211 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194632107491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_41 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41329192388463 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097318077887 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨41, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41329192388463 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097318077887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_42 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (20656121509 / 25000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194640175917 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨42, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (20656121509 / 25000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194640175917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_43 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82590610765947 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194644166641 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨43, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82590610765947 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194644166641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_44 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82556758937431 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (274331023167 / 12500000000000 : ℝ))
      (E := (cell13192 ⟨44, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82556758937431 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (274331023167 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_45 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82522930521261 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194652230361 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨45, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82522930521261 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194652230361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_46 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41244562744197 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194656240923 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨46, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41244562744197 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194656240923 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_47 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82455343809931 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (27433253423 / 1250000000000 : ℝ))
      (E := (cell13192 ⟨47, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82455343809931 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (27433253423 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_48 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82421585457121 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548666066961 / 25000000000000 : ℝ))
      (E := (cell13192 ⟨48, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82421585457121 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548666066961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_49 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41193925200677 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194668279371 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨49, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41193925200677 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194668279371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_50 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82354138614163 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097336152857 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨50, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82354138614163 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097336152857 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_51 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82320450067227 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (43893526879 / 2000000000000 : ℝ))
      (E := (cell13192 ⟨51, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82320450067227 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (43893526879 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_52 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41143392366181 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (68583760371 / 3125000000000 : ℝ))
      (E := (cell13192 ⟨52, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41143392366181 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (68583760371 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_53 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (10281642822691 / 12500000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194684384267 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨53, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (10281642822691 / 12500000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194684384267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_54 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82219523586823 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (219468837941 / 10000000000000 : ℝ))
      (E := (cell13192 ⟨54, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82219523586823 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (219468837941 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_55 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (16437185544097 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (438938486353 / 20000000000000 : ℝ))
      (E := (cell13192 ⟨55, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (16437185544097 / 20000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (438938486353 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_56 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82152354954889 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097348209549 / 50000000000000 : ℝ))
      (E := (cell13192 ⟨56, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82152354954889 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (1097348209549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_57 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (82118805262549 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (17146097309 / 781250000000 : ℝ))
      (E := (cell13192 ⟨57, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (82118805262549 / 100000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (17146097309 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_58 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (20521319654029 / 25000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194704477603 / 100000000000000 : ℝ))
      (E := (cell13192 ⟨58, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (20521319654029 / 25000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (2194704477603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13192_59 : CellCertificate 13192 (873437764212951 / 10000000000000000 : ℝ) (1592190050013143 / 1000000000000000000 : ℝ) (321331712415843 / 10000000000000000 : ℝ)
    (cell13192 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · norm_num [cell13192]
  · have h := gap_lower (n := 13192) (a := (41025887494187 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548677120167 / 25000000000000 : ℝ))
      (E := (cell13192 ⟨59, by decide⟩).energy) (xi := (321331712415843 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13192 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13192]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13192])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13192) (a := (41025887494187 / 50000000000000 : ℝ)) (b := (31214146803 / 20000000000000 : ℝ)) (q := (548677120167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13192])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13192]

theorem cert13193_40 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82692293243563 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (274315246719 / 12500000000000 : ℝ))
      (E := (cell13193 ⟨40, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82692293243563 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (274315246719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_41 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82658371008291 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194525961809 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨41, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82658371008291 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194525961809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_42 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82624472273373 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194529980567 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨42, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82624472273373 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194529980567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_43 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (20647649252331 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438906805763 / 20000000000000 : ℝ))
      (E := (cell13193 ⟨43, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (20647649252331 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438906805763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_44 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41278372593403 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194538046241 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨44, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41278372593403 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194538046241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_45 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82522916776629 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097271045021 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨45, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82522916776629 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097271045021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_46 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (329956446999 / 400000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194546099427 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨46, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (329956446999 / 400000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194546099427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_47 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82455330077271 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194550131213 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨47, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82455330077271 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194550131213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_48 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82421571730439 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548638531033 / 25000000000000 : ℝ))
      (E := (cell13193 ⟨48, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82421571730439 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (548638531033 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_49 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (16477567336129 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194558134621 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨49, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (16477567336129 / 20000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194558134621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_50 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (2573566403107 / 3125000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (219456215997 / 10000000000000 : ℝ))
      (E := (cell13193 ⟨50, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (2573566403107 / 3125000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (219456215997 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_51 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (20580109089613 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194566197259 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨51, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (20580109089613 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194566197259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_52 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82286771029547 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (54864254607 / 2500000000000 : ℝ))
      (E := (cell13193 ⟨52, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82286771029547 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (54864254607 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_53 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (20563282221167 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194574235819 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨53, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (20563282221167 / 25000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194574235819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_54 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82219509895913 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194578230153 / 100000000000000 : ℝ))
      (E := (cell13193 ⟨54, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82219509895913 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (2194578230153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_55 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (256830981361 / 312500000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438916456349 / 20000000000000 : ℝ))
      (E := (cell13193 ⟨55, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (256830981361 / 312500000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438916456349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_56 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (10269042659483 / 12500000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097293134181 / 50000000000000 : ℝ))
      (E := (cell13193 ⟨56, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (10269042659483 / 12500000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (1097293134181 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_57 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (4105939579473 / 5000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438918060829 / 20000000000000 : ℝ))
      (E := (cell13193 ⟨57, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (4105939579473 / 5000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438918060829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_58 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (41042632474479 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (219459432557 / 10000000000000 : ℝ))
      (E := (cell13193 ⟨58, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (41042632474479 / 50000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (219459432557 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13193_59 : CellCertificate 13193 (34936471689749 / 400000000000000 : ℝ) (31841386547159 / 20000000000000000 : ℝ) (64261360607057 / 2000000000000000 : ℝ)
    (cell13193 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · norm_num [cell13193]
  · have h := gap_lower (n := 13193) (a := (82051761327143 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438919677459 / 20000000000000 : ℝ))
      (E := (cell13193 ⟨59, by decide⟩).energy) (xi := (64261360607057 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13193 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13193]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13193])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13193) (a := (82051761327143 / 100000000000000 : ℝ)) (b := (39014692467 / 25000000000000 : ℝ)) (q := (438919677459 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13193])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13193]

theorem cert13194_40 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82692279471007 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (274301479483 / 12500000000000 : ℝ))
      (E := (cell13194 ⟨40, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82692279471007 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (274301479483 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_41 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41329178620873 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194415881333 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨41, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41329178620873 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194415881333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_42 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (16524891702567 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194419898753 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨42, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (16524891702567 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194419898753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_43 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (20647645813697 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438884777369 / 20000000000000 : ℝ))
      (E := (cell13194 ⟨43, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (20647645813697 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438884777369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_44 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82556731438267 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097213951501 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨44, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82556731438267 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097213951501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_45 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41261451517041 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194431945581 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨45, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41261451517041 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194431945581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_46 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82489098013191 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194435953789 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨46, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82489098013191 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194435953789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_47 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41227658173347 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438887996889 / 20000000000000 : ℝ))
      (E := (cell13194 ⟨47, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41227658173347 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438887996889 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_48 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (1030269475073 / 1250000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194443976279 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨48, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (1030269475073 / 1250000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194443976279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_49 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (4119391148101 / 5000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097224022367 / 50000000000000 : ℝ))
      (E := (cell13194 ⟨49, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (4119391148101 / 5000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (1097224022367 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_50 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82354111186767 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438890413823 / 20000000000000 : ℝ))
      (E := (cell13194 ⟨50, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82354111186767 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438890413823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_51 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41160211325879 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194456046429 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨51, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41160211325879 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194456046429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_52 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (20571689332203 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (17555680733 / 800000000000 : ℝ))
      (E := (cell13194 ⟨52, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (20571689332203 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (17555680733 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_53 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41126557594943 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438892816647 / 20000000000000 : ℝ))
      (E := (cell13194 ⟨53, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41126557594943 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (438892816647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_54 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (2055487405177 / 2500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548617033971 / 25000000000000 : ℝ))
      (E := (cell13194 ⟨54, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (2055487405177 / 2500000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548617033971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_55 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82185900352631 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194472127591 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨55, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82185900352631 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194472127591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_56 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (20538081899729 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (109723808633 / 5000000000000 : ℝ))
      (E := (cell13194 ⟨56, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (20538081899729 / 25000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (109723808633 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_57 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (82118777918447 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548620051949 / 25000000000000 : ℝ))
      (E := (cell13194 ⟨57, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (82118777918447 / 100000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (548620051949 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_58 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (41042625641937 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194484228621 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨58, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (41042625641937 / 50000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194484228621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13194_59 : CellCertificate 13194 (436692912020237 / 5000000000000000 : ℝ) (63677944920327 / 40000000000000000 : ℝ) (321281897540049 / 10000000000000000 : ℝ)
    (cell13194 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · norm_num [cell13194]
  · have h := gap_lower (n := 13194) (a := (16410349533597 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194488230551 / 100000000000000 : ℝ))
      (E := (cell13194 ⟨59, by decide⟩).energy) (xi := (321281897540049 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13194 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13194]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13194])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13194) (a := (16410349533597 / 20000000000000 : ℝ)) (b := (156046807561 / 100000000000000 : ℝ)) (q := (2194488230551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13194])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13194]

theorem cert13195_40 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (4134613285027 / 5000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (17554414021 / 800000000000 : ℝ))
      (E := (cell13195 ⟨40, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (4134613285027 / 5000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (17554414021 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_41 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82658343477291 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548576434473 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨41, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82658343477291 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548576434473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_42 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41312222377193 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (68572179811 / 3125000000000 : ℝ))
      (E := (cell13195 ⟨42, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41312222377193 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (68572179811 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_43 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82590569502339 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548578449899 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨43, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82590569502339 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548578449899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_44 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16511343538363 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548579453627 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨44, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16511343538363 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548579453627 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_45 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41261444646811 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (137145115993 / 6250000000000 : ℝ))
      (E := (cell13195 ⟨45, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41261444646811 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (137145115993 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_46 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82489084278717 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438865172589 / 20000000000000 : ℝ))
      (E := (cell13195 ⟨46, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82489084278717 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438865172589 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_47 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (41227651309101 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097164946247 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨47, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (41227651309101 / 50000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097164946247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_48 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (3296861771333 / 4000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548583470817 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨48, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (3296861771333 / 4000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548583470817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_49 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (20596952311369 / 25000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (219433795071 / 10000000000000 : ℝ))
      (E := (cell13195 ⟨49, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (20596952311369 / 25000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (219433795071 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_50 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (8235409747619 / 10000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097170957547 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨50, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (8235409747619 / 10000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097170957547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_51 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (10290051118393 / 12500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097172975257 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨51, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (10290051118393 / 12500000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097172975257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_52 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16457348726031 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438869998967 / 20000000000000 : ℝ))
      (E := (cell13195 ⟨52, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16457348726031 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438869998967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_53 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82253101497183 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438870797123 / 20000000000000 : ℝ))
      (E := (cell13195 ⟨53, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82253101497183 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (438870797123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_54 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (3288779300813 / 4000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (54858950937 / 2500000000000 : ℝ))
      (E := (cell13195 ⟨54, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (3288779300813 / 4000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (54858950937 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_55 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (4109294333591 / 5000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194362028449 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨55, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (4109294333591 / 5000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194362028449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_56 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (82152313924043 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097183036413 / 50000000000000 : ℝ))
      (E := (cell13195 ⟨56, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (82152313924043 / 100000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (1097183036413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_57 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (20529691062377 / 25000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548592526829 / 25000000000000 : ℝ))
      (E := (cell13195 ⟨57, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (20529691062377 / 25000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (548592526829 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_58 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (16417047524173 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (109718706377 / 5000000000000 : ℝ))
      (E := (cell13195 ⟨58, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (16417047524173 / 20000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (109718706377 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13195_59 : CellCertificate 13195 (873359859602341 / 10000000000000000 : ℝ) (1591827936959657 / 1000000000000000000 : ℝ) (16062849796459 / 500000000000000 : ℝ)
    (cell13195 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · norm_num [cell13195]
  · have h := gap_lower (n := 13195) (a := (820517340109 / 1000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194378128917 / 100000000000000 : ℝ))
      (E := (cell13195 ⟨59, by decide⟩).energy) (xi := (16062849796459 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13195 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13195]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13195])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13195) (a := (820517340109 / 1000000000000 : ℝ)) (b := (156034847093 / 100000000000000 : ℝ)) (q := (2194378128917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13195])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13195]

theorem cert13196_40 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82692251932163 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (54854791631 / 2500000000000 : ℝ))
      (E := (cell13196 ⟨40, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82692251932163 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (54854791631 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_41 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (20664582428731 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097097853971 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨41, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (20664582428731 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097097853971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_42 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (10328053874753 / 12500000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (219419972269 / 10000000000000 : ℝ))
      (E := (cell13196 ⟨42, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (10328053874753 / 12500000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (219419972269 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_43 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41295277875989 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097101854101 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨43, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41295277875989 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097101854101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_44 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82556703947449 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194207721871 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨44, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82556703947449 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194207721871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_45 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41261437777623 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097105881027 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨45, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41261437777623 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097105881027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_46 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82489070546327 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194215767959 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨46, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82489070546327 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194215767959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_47 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82455288891793 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097109898201 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨47, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82455288891793 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097109898201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_48 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82421530562891 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (21942238451 / 1000000000000 : ℝ))
      (E := (cell13196 ⟨48, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82421530562891 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (21942238451 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_49 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41193897765507 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097113926273 / 50000000000000 : ℝ))
      (E := (cell13196 ⟨49, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41193897765507 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (1097113926273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_50 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (16470816753539 / 20000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194231874991 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨50, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (16470816753539 / 20000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194231874991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_51 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (8232039524461 / 10000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (438847181903 / 20000000000000 : ℝ))
      (E := (cell13196 ⟨51, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (8232039524461 / 10000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (438847181903 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_52 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (41143364966789 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548559973477 / 25000000000000 : ℝ))
      (E := (cell13196 ⟨52, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (41143364966789 / 50000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (548559973477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_53 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82253087806557 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194243942959 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨53, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82253087806557 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194243942959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_54 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82219468835647 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (109712396747 / 5000000000000 : ℝ))
      (E := (cell13196 ⟨54, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82219468835647 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (109712396747 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_55 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (20546468248271 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194251984319 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨55, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (20546468248271 / 25000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194251984319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_56 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (16430460050249 / 20000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194255968859 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨56, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (16430460050249 / 20000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194255968859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_57 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82118750582643 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (137141250169 / 6250000000000 : ℝ))
      (E := (cell13196 ⟨57, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82118750582643 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (137141250169 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_58 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (82085223959929 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194264022329 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨58, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (82085223959929 / 100000000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194264022329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13196_59 : CellCertificate 13196 (436666949464233 / 5000000000000000 : ℝ) (795853634604117 / 500000000000000000 : ℝ) (160616049100861 / 5000000000000000 : ℝ)
    (cell13196 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · norm_num [cell13196]
  · have h := gap_lower (n := 13196) (a := (5128232522243 / 6250000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194268023151 / 100000000000000 : ℝ))
      (E := (cell13196 ⟨59, by decide⟩).energy) (xi := (160616049100861 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13196 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13196]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13196])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13196) (a := (5128232522243 / 6250000000000 : ℝ)) (b := (31204577693 / 20000000000000 : ℝ)) (q := (2194268023151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13196])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13196]

theorem cert13197_40 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (661537905327 / 800000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194081573709 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨40, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (661537905327 / 800000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194081573709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_41 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16531663190929 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219408561503 / 10000000000000 : ℝ))
      (E := (cell13197 ⟨41, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16531663190929 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219408561503 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_42 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (13219906759 / 16000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097044814221 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨42, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (13219906759 / 16000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097044814221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_43 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82590542003703 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194093671531 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨43, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82590542003703 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194093671531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_44 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (5159793137823 / 6250000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (109704884199 / 5000000000000 : ℝ))
      (E := (cell13197 ⟨44, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (5159793137823 / 6250000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (109704884199 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_45 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16504572363791 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219410172299 / 10000000000000 : ℝ))
      (E := (cell13197 ⟨45, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16504572363791 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219410172299 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_46 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (4124452840801 / 5000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274263215971 / 12500000000000 : ℝ))
      (E := (cell13197 ⟨46, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (4124452840801 / 5000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (274263215971 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_47 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (41227637583733 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194109755131 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨47, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (41227637583733 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194109755131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_48 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (4121075842227 / 5000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194113743811 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨48, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (4121075842227 / 5000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194113743811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_49 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82387781818633 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (438823550049 / 20000000000000 : ℝ))
      (E := (cell13197 ⟨49, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82387781818633 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (438823550049 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_50 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82354070061279 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548530442931 / 25000000000000 : ℝ))
      (E := (cell13197 ⟨50, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82354070061279 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548530442931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_51 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16464076308831 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194125805327 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨51, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16464076308831 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194125805327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_52 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82286716239079 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097064923961 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨52, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82286716239079 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097064923961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_53 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82253074118009 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548533459267 / 25000000000000 : ℝ))
      (E := (cell13197 ⟨53, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82253074118009 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548533459267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_54 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16443891030609 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194137887391 / 100000000000000 : ℝ))
      (E := (cell13197 ⟨54, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16443891030609 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (2194137887391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_55 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (10273232414553 / 12500000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219414187691 / 10000000000000 : ℝ))
      (E := (cell13197 ⟨55, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (10273232414553 / 12500000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219414187691 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_56 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (41076143290261 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219414591993 / 10000000000000 : ℝ))
      (E := (cell13197 ⟨56, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (41076143290261 / 50000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (219414591993 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_57 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (20529684229463 / 25000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097074976577 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨57, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (20529684229463 / 25000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097074976577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_58 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (16417042060213 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548538493051 / 25000000000000 : ℝ))
      (E := (cell13197 ⟨58, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (16417042060213 / 20000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (548538493051 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13197_59 : CellCertificate 13197 (873307942017991 / 10000000000000000 : ℝ) (1591586619749743 / 1000000000000000000 : ℝ) (4015090054459 / 125000000000000 : ℝ)
    (cell13197 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · norm_num [cell13197]
  · have h := gap_lower (n := 13197) (a := (82051706702947 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097078986249 / 50000000000000 : ℝ))
      (E := (cell13197 ⟨59, by decide⟩).energy) (xi := (4015090054459 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13197 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13197]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13197])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13197) (a := (82051706702947 / 100000000000000 : ℝ)) (b := (39002732919 / 25000000000000 : ℝ)) (q := (1097078986249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13197])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13197]

theorem cert13198_40 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (20673056100419 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193971536829 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨40, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (20673056100419 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193971536829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_41 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41329151098227 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193975576793 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨41, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41329151098227 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193975576793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_42 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41312201745781 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438795917779 / 20000000000000 : ℝ))
      (E := (cell13198 ⟨42, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41312201745781 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438795917779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_43 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41295264128757 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096991815359 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨43, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41295264128757 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1096991815359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_44 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82556676464973 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193987641949 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨44, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82556676464973 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193987641949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_45 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (20630712021187 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193991679787 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨45, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (20630712021187 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193991679787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_46 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82489043087797 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193995683439 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨46, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82489043087797 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193995683439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_47 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41227630722611 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193999709721 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨47, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41227630722611 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2193999709721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_48 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (8242150312827 / 10000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194003697367 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨48, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (8242150312827 / 10000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194003697367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_49 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (20596942027083 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1097003851407 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨49, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (20596942027083 / 25000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1097003851407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_50 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82354056356943 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194011723351 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨50, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82354056356943 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194011723351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_51 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41160183922889 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1097007878029 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨51, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41160183922889 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1097007878029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_52 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82286702546657 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194019797803 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨52, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82286702546657 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194019797803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_53 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41126530215769 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438804757229 / 20000000000000 : ℝ))
      (E := (cell13198 ⟨53, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41126530215769 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (438804757229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_54 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82219441472519 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (219402783571 / 10000000000000 : ℝ))
      (E := (cell13198 ⟨54, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82219441472519 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (219402783571 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_55 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82185845641839 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (137126992729 / 6250000000000 : ℝ))
      (E := (cell13198 ⟨55, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82185845641839 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (137126992729 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_56 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (82152272911873 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194035866871 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨56, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (82152272911873 / 100000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194035866871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_57 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (16423744651027 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1097019949737 / 50000000000000 : ℝ))
      (E := (cell13198 ⟨57, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (16423744651027 / 20000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (1097019949737 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_58 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41042598322137 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194043917951 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨58, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41042598322137 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194043917951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13198_59 : CellCertificate 13198 (109160248608757 / 1250000000000000 : ℝ) (1591465988580027 / 1000000000000000000 : ℝ) (321182314393219 / 10000000000000000 : ℝ)
    (cell13198 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · norm_num [cell13198]
  · have h := gap_lower (n := 13198) (a := (41025846526039 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194047917717 / 100000000000000 : ℝ))
      (E := (cell13198 ⟨59, by decide⟩).energy) (xi := (321182314393219 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13198 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13198]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13198])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13198) (a := (41025846526039 / 50000000000000 : ℝ)) (b := (6239959069 / 4000000000000 : ℝ)) (q := (2194047917717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13198])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13198]

theorem cert13199_40 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41346105319783 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (10969307773 / 500000000000 : ℝ))
      (E := (cell13199 ⟨40, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41346105319783 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (10969307773 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_41 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82658288440351 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (438773106883 / 20000000000000 : ℝ))
      (E := (cell13199 ⟨41, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82658288440351 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (438773106883 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_42 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82624389741461 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193869545207 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨42, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82624389741461 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193869545207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_43 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82590514513411 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096936792883 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨43, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82590514513411 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096936792883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_44 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41278331363431 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193877595779 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨44, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41278331363431 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193877595779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_45 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (660182674821 / 800000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096940816223 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨45, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (660182674821 / 800000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096940816223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_46 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82489029361657 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548471408743 / 25000000000000 : ℝ))
      (E := (cell13199 ⟨46, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82489029361657 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548471408743 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_47 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (4122762386253 / 5000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (87755586407 / 4000000000000 : ℝ))
      (E := (cell13199 ⟨47, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (4122762386253 / 5000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (87755586407 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_48 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82421489414081 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219389370577 / 10000000000000 : ℝ))
      (E := (cell13199 ⟨48, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82421489414081 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219389370577 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_49 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (5149234650007 / 6250000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193897710253 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨49, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (5149234650007 / 6250000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193897710253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_50 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41177021327343 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193901729873 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨50, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41177021327343 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193901729873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_51 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (2058008853737 / 2500000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548476440427 / 25000000000000 : ℝ))
      (E := (cell13199 ⟨51, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (2058008853737 / 2500000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548476440427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_52 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82286688856313 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (34279839743 / 1562500000000 : ℝ))
      (E := (cell13199 ⟨52, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82286688856313 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (34279839743 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_53 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82253046747143 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219391379019 / 10000000000000 : ℝ))
      (E := (cell13199 ⟨53, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82253046747143 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (219391379019 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_54 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82219427794069 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096958919511 / 50000000000000 : ℝ))
      (E := (cell13199 ⟨54, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82219427794069 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (1096958919511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_55 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (82185831969329 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193921827141 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨55, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (82185831969329 / 100000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193921827141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_56 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (41076129622649 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193925868853 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨56, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (41076129622649 / 50000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193925868853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_57 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (8211870959449 / 10000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193929900861 / 100000000000000 : ℝ))
      (E := (cell13199 ⟨57, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (8211870959449 / 10000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (2193929900861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_58 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (16417036597911 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548483479697 / 25000000000000 : ℝ))
      (E := (cell13199 ⟨58, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (16417036597911 / 20000000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (548483479697 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

theorem cert13199_59 : CellCertificate 13199 (873256039483803 / 10000000000000000 : ℝ) (795672687847463 / 500000000000000000 : ℝ) (160578714155133 / 5000000000000000 : ℝ)
    (cell13199 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · norm_num [cell13199]
  · have h := gap_lower (n := 13199) (a := (1025645992541 / 1250000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (43878758361 / 2000000000000 : ℝ))
      (E := (cell13199 ⟨59, by decide⟩).energy) (xi := (160578714155133 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell13199 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell13199]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell13199])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 13199) (a := (1025645992541 / 1250000000000 : ℝ)) (b := (155987023611 / 100000000000000 : ℝ)) (q := (43878758361 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell13199])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell13199]

end BstLean.Part268
