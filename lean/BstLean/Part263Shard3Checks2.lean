import BstLean.Part263Shard3Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12300_40 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82697236189657 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (288033647701 / 12500000000000 : ℝ))
      (E := (cell12300 ⟨40, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82697236189657 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (288033647701 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_41 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20665776949169 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (57606829381 / 2500000000000 : ℝ))
      (E := (cell12300 ⟨41, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20665776949169 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (57606829381 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_42 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41314501593959 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304277186133 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨42, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41314501593959 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304277186133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_43 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82594922333381 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460856242827 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨43, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82594922333381 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460856242827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_44 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20640216300803 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152142600039 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨44, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20640216300803 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152142600039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_45 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82526831767709 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152144601063 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨45, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82526831767709 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152144601063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_46 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20623205499331 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152146580311 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨46, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20623205499331 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152146580311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_47 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20614708965663 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460859438443 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨47, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20614708965663 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460859438443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_48 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82424873334441 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152150588971 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨48, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82424873334441 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152150588971 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_49 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (2574716699487 / 3125000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152152587597 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨49, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (2574716699487 / 3125000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152152587597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_50 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82357018981121 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (23043091823 / 1000000000000 : ℝ))
      (E := (cell12300 ⟨50, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82357018981121 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (23043091823 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_51 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41161563549119 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (230431319737 / 10000000000000 : ℝ))
      (E := (cell12300 ⟨51, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41161563549119 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (230431319737 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_52 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (41144629353133 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460863431863 / 20000000000000 : ℝ))
      (E := (cell12300 ⟨52, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (41144629353133 / 50000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (460863431863 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_53 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (2056385344417 / 2500000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304321183777 / 100000000000000 : ℝ))
      (E := (cell12300 ⟨53, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (2056385344417 / 2500000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (2304321183777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_54 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (10277699035137 / 12500000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576081287557 / 25000000000000 : ℝ))
      (E := (cell12300 ⟨54, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (10277699035137 / 12500000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576081287557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_55 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (3287511767651 / 4000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152164586991 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨55, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (3287511767651 / 4000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152164586991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_56 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82154019479119 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152166566997 / 50000000000000 : ℝ))
      (E := (cell12300 ⟨56, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82154019479119 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (1152166566997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_57 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (82120268116669 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576084286313 / 25000000000000 : ℝ))
      (E := (cell12300 ⟨57, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (82120268116669 / 100000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (576084286313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_58 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20521635019027 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (230434114533 / 10000000000000 : ℝ))
      (E := (cell12300 ⟨58, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20521635019027 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (230434114533 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12300_59 : CellCertificate 12300 (898214247379509 / 10000000000000000 : ℝ) (853847694767541 / 500000000000000000 : ℝ) (34522299965143 / 1000000000000000 : ℝ)
    (cell12300 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · norm_num [cell12300]
  · have h := gap_lower (n := 12300) (a := (20513208832439 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (72010785333 / 3125000000000 : ℝ))
      (E := (cell12300 ⟨59, by decide⟩).energy) (xi := (34522299965143 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12300 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12300]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12300])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12300) (a := (20513208832439 / 25000000000000 : ℝ)) (b := (5235369359 / 3125000000000 : ℝ)) (q := (72010785333 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12300])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12300]

theorem cert12301_40 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (10337154143621 / 12500000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (288015755733 / 12500000000000 : ℝ))
      (E := (cell12301 ⟨40, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (10337154143621 / 12500000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (288015755733 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_41 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (8266310507393 / 10000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304130068543 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨41, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (8266310507393 / 10000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304130068543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_42 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (20657250195669 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (230413405049 / 10000000000000 : ℝ))
      (E := (cell12301 ⟨42, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (20657250195669 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (230413405049 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_43 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41297460122601 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460827610053 / 20000000000000 : ℝ))
      (E := (cell12301 ⟨43, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41297460122601 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460827610053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_44 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82560863431657 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460828413499 / 20000000000000 : ℝ))
      (E := (cell12301 ⟨44, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82560863431657 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460828413499 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_45 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41263415156171 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460829208553 / 20000000000000 : ℝ))
      (E := (cell12301 ⟨45, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41263415156171 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460829208553 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_46 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41246410428853 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460830006809 / 20000000000000 : ℝ))
      (E := (cell12301 ⟨46, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41246410428853 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (460830006809 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_47 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (20614708759587 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304154040309 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨47, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (20614708759587 / 25000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304154040309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_48 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (10303109103127 / 12500000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152079030157 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨48, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (10303109103127 / 12500000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152079030157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_49 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41195467094301 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576040508421 / 25000000000000 : ℝ))
      (E := (cell12301 ⟨49, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41195467094301 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (576040508421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_50 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82357019100149 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144010376101 / 6250000000000 : ℝ))
      (E := (cell12301 ⟨50, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82357019100149 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144010376101 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_51 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82323127530843 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152085005111 / 50000000000000 : ℝ))
      (E := (cell12301 ⟨51, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82323127530843 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (1152085005111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_52 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (16457851890403 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304174009401 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨52, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (16457851890403 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304174009401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_53 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82255414835141 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304178012839 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨53, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82255414835141 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304178012839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_54 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82221593651839 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (230418201801 / 10000000000000 : ℝ))
      (E := (cell12301 ⟨54, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82221593651839 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (230418201801 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_55 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82187795873869 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304186022177 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨55, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82187795873869 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304186022177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_56 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (16430804294627 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304190022391 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨56, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (16430804294627 / 20000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304190022391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_57 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (41060135210839 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304194015497 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨57, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (41060135210839 / 50000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304194015497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_58 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82086542691681 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144012374883 / 6250000000000 : ℝ))
      (E := (cell12301 ⟨58, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82086542691681 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (144012374883 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12301_59 : CellCertificate 12301 (359273815739 / 4000000000000 : ℝ) (853778258336673 / 500000000000000000 : ℝ) (345194191837763 / 10000000000000000 : ℝ)
    (cell12301 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · norm_num [cell12301]
  · have h := gap_lower (n := 12301) (a := (82052838255467 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304202025863 / 100000000000000 : ℝ))
      (E := (cell12301 ⟨59, by decide⟩).energy) (xi := (345194191837763 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12301 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12301]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12301])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12301) (a := (82052838255467 / 100000000000000 : ℝ)) (b := (167518019793 / 100000000000000 : ℝ)) (q := (2304202025863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12301])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12301]

theorem cert12302_40 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (5168576881829 / 6250000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (57599574131 / 2500000000000 : ℝ))
      (E := (cell12302 ⟨40, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (5168576881829 / 6250000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (57599574131 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_41 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82663102352129 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (230398701703 / 10000000000000 : ℝ))
      (E := (cell12302 ⟨41, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82663102352129 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (230398701703 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_42 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82628998378337 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303990970099 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨42, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82628998378337 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303990970099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_43 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82594918157887 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151997500243 / 50000000000000 : ℝ))
      (E := (cell12302 ⟨43, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82594918157887 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1151997500243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_44 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (322503365863 / 390625000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303998990289 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨44, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (322503365863 / 390625000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2303998990289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_45 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82526828857761 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (230400299767 / 10000000000000 : ℝ))
      (E := (cell12302 ⟨45, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82526828857761 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (230400299767 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_46 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (16498563943767 / 20000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1152003481487 / 50000000000000 : ℝ))
      (E := (cell12302 ⟨46, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (16498563943767 / 20000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1152003481487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_47 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (2576838569211 / 3125000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304010943973 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨47, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (2576838569211 / 3125000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304010943973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_48 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41212436158129 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (92160597577 / 4000000000000 : ℝ))
      (E := (cell12302 ⟨48, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41212436158129 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (92160597577 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_49 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82390933994249 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304018947871 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨49, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82390933994249 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304018947871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_50 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41178509609883 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (576005741909 / 25000000000000 : ℝ))
      (E := (cell12302 ⟨50, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41178509609883 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (576005741909 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_51 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82323127963997 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1152013468933 / 50000000000000 : ℝ))
      (E := (cell12302 ⟨51, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82323127963997 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1152013468933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_52 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41144630099137 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1152015487183 / 50000000000000 : ℝ))
      (E := (cell12302 ⟨52, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41144630099137 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (1152015487183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_53 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82255415894073 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (576008739217 / 25000000000000 : ℝ))
      (E := (cell12302 ⟨53, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82255415894073 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (576008739217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_54 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82221595023013 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304038941809 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨54, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82221595023013 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304038941809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_55 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (10273474694607 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (576010731613 / 25000000000000 : ℝ))
      (E := (cell12302 ⟨55, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (10273474694607 / 12500000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (576010731613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_56 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (5134626466719 / 6250000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304046966933 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨56, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (5134626466719 / 6250000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304046966933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_57 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (41060136363501 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304050941949 / 100000000000000 : ℝ))
      (E := (cell12302 ⟨57, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (41060136363501 / 50000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (2304050941949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_58 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (20521636326883 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (92162198653 / 4000000000000 : ℝ))
      (E := (cell12302 ⟨58, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (20521636326883 / 25000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (92162198653 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12302_59 : CellCertificate 12302 (898154835967631 / 10000000000000000 : ℝ) (1707417666396553 / 1000000000000000000 : ℝ) (172582694473749 / 5000000000000000 : ℝ)
    (cell12302 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · norm_num [cell12302]
  · have h := gap_lower (n := 12302) (a := (82052841181417 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (288007364781 / 12500000000000 : ℝ))
      (E := (cell12302 ⟨59, by decide⟩).energy) (xi := (172582694473749 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12302 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12302]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12302])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12302) (a := (82052841181417 / 100000000000000 : ℝ)) (b := (104690139 / 62500000000 : ℝ)) (q := (288007364781 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12302])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12302]

theorem cert12303_40 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41348613535271 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151919999223 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨40, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41348613535271 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151919999223 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_41 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82663099631271 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460768804141 / 20000000000000 : ℝ))
      (E := (cell12303 ⟨41, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82663099631271 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460768804141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_42 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82628995974903 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (17998812529 / 781250000000 : ℝ))
      (E := (cell12303 ⟨42, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82628995974903 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (17998812529 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_43 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82594916071437 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151926003011 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨43, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82594916071437 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151926003011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_44 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (5160053743189 / 6250000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151927984231 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨44, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (5160053743189 / 6250000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151927984231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_45 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20631706850991 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (115193000401 / 5000000000000 : ℝ))
      (E := (cell12303 ⟨45, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20631706850991 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (115193000401 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_46 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (8249281858071 / 10000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303864006259 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨46, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (8249281858071 / 10000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303864006259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_47 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82458833391861 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303867962081 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨47, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82458833391861 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303867962081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_48 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82424871808167 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151935995981 / 50000000000000 : ℝ))
      (E := (cell12303 ⟨48, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82424871808167 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (1151935995981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_49 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41195466900261 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303875976677 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨49, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41195466900261 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303875976677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_50 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82357019339971 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (115193998671 / 5000000000000 : ℝ))
      (E := (cell12303 ⟨50, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82357019339971 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (115193998671 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_51 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (823231283977 / 1000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303883980303 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨51, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (823231283977 / 1000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303883980303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_52 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82289260945043 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303887936233 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨52, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82289260945043 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303887936233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_53 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20563854238369 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303891956851 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨53, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20563854238369 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303891956851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_54 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (4111079819731 / 5000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303895980663 / 100000000000000 : ℝ))
      (E := (cell12303 ⟨54, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (4111079819731 / 5000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (2303895980663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_55 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20546949810059 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230389994587 / 10000000000000 : ℝ))
      (E := (cell12303 ⟨55, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20546949810059 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230389994587 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_56 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (20538506365557 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (115195198381 / 5000000000000 : ℝ))
      (E := (cell12303 ⟨56, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (20538506365557 / 25000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (115195198381 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_57 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82120275032641 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230390792461 / 10000000000000 : ℝ))
      (E := (cell12303 ⟨57, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82120275032641 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (230390792461 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_58 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (41043273961829 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460782386333 / 20000000000000 : ℝ))
      (E := (cell12303 ⟨58, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (41043273961829 / 50000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (460782386333 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12303_59 : CellCertificate 12303 (898125137238757 / 10000000000000000 : ℝ) (853639419349597 / 500000000000000000 : ℝ) (43142073872401 / 1250000000000000 : ℝ)
    (cell12303 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · norm_num [cell12303]
  · have h := gap_lower (n := 12303) (a := (82052844107603 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (18431327409 / 800000000000 : ℝ))
      (E := (cell12303 ⟨59, by decide⟩).energy) (xi := (43142073872401 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12303 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12303]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12303])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12303) (a := (82052844107603 / 100000000000000 : ℝ)) (b := (41872606827 / 25000000000000 : ℝ)) (q := (18431327409 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12303])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12303]

theorem cert12304_40 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (20674306008201 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (92147883471 / 4000000000000 : ℝ))
      (E := (cell12304 ⟨40, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (20674306008201 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (92147883471 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_41 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (82663096911357 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151850539783 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨41, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (82663096911357 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151850539783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_42 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (20657248393093 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303705092577 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨42, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (20657248393093 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303705092577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_43 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (82594913985851 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (3685934507 / 160000000000 : ℝ))
      (E := (cell12304 ⟨43, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (82594913985851 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (3685934507 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_44 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (82560858121943 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151856530409 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨44, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (82560858121943 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151856530409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_45 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (10315853243869 / 12500000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151858536907 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨45, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (10315853243869 / 12500000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151858536907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_46 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (8249281744333 / 10000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575930261551 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨46, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (8249281744333 / 10000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575930261551 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_47 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (20614708142419 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151862517881 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨47, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (20614708142419 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151862517881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_48 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41212435650371 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151864520621 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨48, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41212435650371 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151864520621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_49 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (80459896101 / 97656250000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303733061183 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨49, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (80459896101 / 97656250000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303733061183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_50 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (20589254865191 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (287967129371 / 12500000000000 : ℝ))
      (E := (cell12304 ⟨50, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (20589254865191 / 25000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (287967129371 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_51 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (5145195551997 / 6250000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151870509801 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨51, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (5145195551997 / 6250000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151870509801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_52 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (82289261692321 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575936267993 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨52, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (82289261692321 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575936267993 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_53 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (1645108360267 / 2000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303749071803 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨53, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (1645108360267 / 2000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303749071803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_54 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (41110798883329 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303753016499 / 100000000000000 : ℝ))
      (E := (cell12304 ⟨54, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (41110798883329 / 50000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (2303753016499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_55 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (10273475115501 / 12500000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (230375702137 / 10000000000000 : ℝ))
      (E := (cell12304 ⟨55, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (10273475115501 / 12500000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (230375702137 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_56 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (16430805491461 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151880512227 / 50000000000000 : ℝ))
      (E := (cell12304 ⟨56, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (16430805491461 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (1151880512227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_57 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (16424055467719 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575941255647 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨57, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (16424055467719 / 20000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575941255647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_58 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (82086550540061 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (287971126551 / 12500000000000 : ℝ))
      (E := (cell12304 ⟨58, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (82086550540061 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (287971126551 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12304_59 : CellCertificate 12304 (179619088631947 / 2000000000000000 : ℝ) (1707140033575761 / 1000000000000000000 : ℝ) (345107797931471 / 10000000000000000 : ℝ)
    (cell12304 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · norm_num [cell12304]
  · have h := gap_lower (n := 12304) (a := (82052847034027 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575943262373 / 25000000000000 : ℝ))
      (E := (cell12304 ⟨59, by decide⟩).energy) (xi := (345107797931471 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12304 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12304]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12304])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12304) (a := (82052847034027 / 100000000000000 : ℝ)) (b := (167476634517 / 100000000000000 : ℝ)) (q := (575943262373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12304])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12304]

theorem cert12305_40 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82697220996049 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (230355423023 / 10000000000000 : ℝ))
      (E := (cell12305 ⟨40, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82697220996049 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (230355423023 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_41 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (16532618838477 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (46071165047 / 2000000000000 : ℝ))
      (E := (cell12305 ⟨41, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (16532618838477 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (46071165047 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_42 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (16525798234149 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303562236697 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨42, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (16525798234149 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303562236697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_43 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82594911901129 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303566241823 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨43, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82594911901129 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303566241823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_44 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (10320107044211 / 12500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (575892552139 / 25000000000000 : ℝ))
      (E := (cell12305 ⟨44, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (10320107044211 / 12500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (575892552139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_45 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (3301072979949 / 4000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460714839011 / 20000000000000 : ℝ))
      (E := (cell12305 ⟨45, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (3301072979949 / 4000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460714839011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_46 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (16498563261339 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303578200509 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨46, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (16498563261339 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303578200509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_47 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82458831748197 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (230358222389 / 10000000000000 : ℝ))
      (E := (cell12305 ⟨47, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82458831748197 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (230358222389 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_48 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (321972151539 / 390625000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460717241011 / 20000000000000 : ℝ))
      (E := (cell12305 ⟨48, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (321972151539 / 390625000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460717241011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_49 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (10298866676869 / 12500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (143974387587 / 6250000000000 : ℝ))
      (E := (cell12305 ⟨49, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (10298866676869 / 12500000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (143974387587 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_50 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (16471403916429 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151797105613 / 50000000000000 : ℝ))
      (E := (cell12305 ⟨50, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (16471403916429 / 20000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (1151797105613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_51 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82323129266753 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (287949779083 / 12500000000000 : ℝ))
      (E := (cell12305 ⟨51, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82323129266753 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (287949779083 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_52 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82289262440109 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460720440923 / 20000000000000 : ℝ))
      (E := (cell12305 ⟨52, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82289262440109 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (460720440923 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_53 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (41127709536847 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (23036061837 / 1000000000000 : ℝ))
      (E := (cell12305 ⟨53, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (41127709536847 / 50000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (23036061837 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_54 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82221599139127 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303610226431 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨54, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82221599139127 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303610226431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_55 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82187802608173 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (143975888251 / 6250000000000 : ℝ))
      (E := (cell12305 ⟨55, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82187802608173 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (143975888251 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_56 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (1283656710199 / 1562500000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303618196519 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨56, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (1283656710199 / 1562500000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303618196519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_57 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82120279644863 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303622176779 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨57, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82120279644863 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303622176779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_58 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (82086553156739 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303626208559 / 100000000000000 : ℝ))
      (E := (cell12305 ⟨58, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (82086553156739 / 100000000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (2303626208559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12305_59 : CellCertificate 12305 (898065753729421 / 10000000000000000 : ℝ) (6828005004083 / 4000000000000000 : ℝ) (345079009802861 / 10000000000000000 : ℝ)
    (cell12305 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · norm_num [cell12305]
  · have h := gap_lower (n := 12305) (a := (5128303122543 / 6250000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (575907542511 / 25000000000000 : ℝ))
      (E := (cell12305 ⟨59, by decide⟩).energy) (xi := (345079009802861 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12305 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12305]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12305])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12305) (a := (5128303122543 / 6250000000000 : ℝ)) (b := (6698513761 / 4000000000000 : ℝ)) (q := (575907542511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12305])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12305]

theorem cert12306_40 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20674304490069 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303411487519 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨40, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20674304490069 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303411487519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_41 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82663091474357 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575853870081 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨41, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82663091474357 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575853870081 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_42 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82628988770021 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151709747413 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨42, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82628988770021 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151709747413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_43 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (8259490981727 / 10000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575855868023 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨43, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (8259490981727 / 10000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575855868023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_44 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (5160053411641 / 6250000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303427470479 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨44, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (5160053411641 / 6250000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303427470479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_45 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82526823047283 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (287928928821 / 12500000000000 : ℝ))
      (E := (cell12306 ⟨45, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82526823047283 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (287928928821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_46 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (16498563034161 / 20000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151717734587 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨46, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (16498563034161 / 20000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151717734587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_47 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (1288419233241 / 1562500000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303439467593 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨47, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (1288419233241 / 1562500000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303439467593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_48 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20606217571973 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575860856127 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨48, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20606217571973 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575860856127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_49 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82390933223107 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (92137898249 / 4000000000000 : ℝ))
      (E := (cell12306 ⟨49, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82390933223107 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (92137898249 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_50 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82357019704113 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575862860813 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨50, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82357019704113 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575862860813 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_51 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82323129702101 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303455442593 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨51, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82323129702101 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303455442593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_52 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82289263188407 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151729726071 / 50000000000000 : ℝ))
      (E := (cell12306 ⟨52, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82289263188407 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (1151729726071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_53 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20563855033627 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303463410569 / 100000000000000 : ℝ))
      (E := (cell12306 ⟨53, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20563855033627 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (2303463410569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_54 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (20555400128007 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575866858337 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨54, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (20555400128007 / 25000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575866858337 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_55 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (8218780429273 / 10000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575867864687 / 25000000000000 : ℝ))
      (E := (cell12306 ⟨55, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (8218780429273 / 10000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (575867864687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_56 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (2053850786213 / 2500000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460695084947 / 20000000000000 : ℝ))
      (E := (cell12306 ⟨56, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (2053850786213 / 2500000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460695084947 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_57 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (41060140975723 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230347944629 / 10000000000000 : ℝ))
      (E := (cell12306 ⟨57, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (41060140975723 / 50000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (230347944629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_58 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82086555773693 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460696680371 / 20000000000000 : ℝ))
      (E := (cell12306 ⟨58, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82086555773693 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (460696680371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12306_59 : CellCertificate 12306 (89803606894667 / 1000000000000000 : ℝ) (1706862491028657 / 1000000000000000000 : ℝ) (345050226591957 / 10000000000000000 : ℝ)
    (cell12306 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · norm_num [cell12306]
  · have h := gap_lower (n := 12306) (a := (82052852887587 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (287935925761 / 12500000000000 : ℝ))
      (E := (cell12306 ⟨59, by decide⟩).energy) (xi := (345050226591957 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12306 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12306]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12306])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12306) (a := (82052852887587 / 100000000000000 : ℝ)) (b := (20931131979 / 12500000000000 : ℝ)) (q := (287935925761 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12306])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12306]

theorem cert12307_40 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41348607462743 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460653759987 / 20000000000000 : ℝ))
      (E := (cell12307 ⟨40, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41348607462743 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460653759987 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_41 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82663088757271 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (230327276349 / 10000000000000 : ℝ))
      (E := (cell12307 ⟨41, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82663088757271 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (230327276349 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_42 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (413144931851 / 500000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303276749457 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨42, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (413144931851 / 500000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303276749457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_43 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41297453867137 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151640378841 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨43, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41297453867137 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151640378841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_44 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82560852819647 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303284787789 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨44, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82560852819647 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303284787789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_45 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (5157926349789 / 6250000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303288780357 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨45, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (5157926349789 / 6250000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303288780357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_46 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82492814035659 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (287911591813 / 12500000000000 : ℝ))
      (E := (cell12307 ⟨46, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82492814035659 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (287911591813 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_47 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (20614707526839 / 25000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151648383437 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨47, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (20614707526839 / 25000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151648383437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_48 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41212434891233 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151650379249 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨48, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41212434891233 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151650379249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_49 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82390933031889 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151652383381 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨49, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82390933031889 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151652383381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_50 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82357019826669 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151654365523 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨50, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82357019826669 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151654365523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_51 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82323130137999 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303312767319 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨51, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82323130137999 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303312767319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_52 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82289263937213 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151658377783 / 50000000000000 : ℝ))
      (E := (cell12307 ⟨52, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82289263937213 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (1151658377783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_53 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (5140963824737 / 6250000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575830188103 / 25000000000000 : ℝ))
      (E := (cell12307 ⟨53, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (5140963824737 / 6250000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575830188103 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_54 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82221601885359 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303324755327 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨54, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82221601885359 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303324755327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_55 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82187805977679 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (71979023799 / 3125000000000 : ℝ))
      (E := (cell12307 ⟨55, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82187805977679 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (71979023799 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_56 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41077016722329 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460666553637 / 20000000000000 : ℝ))
      (E := (cell12307 ⟨56, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41077016722329 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (460666553637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_57 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82120284258343 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575834178227 / 25000000000000 : ℝ))
      (E := (cell12307 ⟨57, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82120284258343 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (575834178227 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_58 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (82086558390923 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303340710559 / 100000000000000 : ℝ))
      (E := (cell12307 ⟨58, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (82086558390923 / 100000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (2303340710559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12307_59 : CellCertificate 12307 (449003194405171 / 5000000000000000 : ℝ) (1706723753593979 / 1000000000000000000 : ℝ) (43127681037167 / 1250000000000000 : ℝ)
    (cell12307 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · norm_num [cell12307]
  · have h := gap_lower (n := 12307) (a := (41026427907361 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (230334475763 / 10000000000000 : ℝ))
      (E := (cell12307 ⟨59, by decide⟩).energy) (xi := (43127681037167 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12307 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12307]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12307])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12307) (a := (41026427907361 / 50000000000000 : ℝ)) (b := (167435269937 / 100000000000000 : ℝ)) (q := (230334475763 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12307])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12307]

theorem cert12308_40 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41348605945839 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303126167481 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨40, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41348605945839 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303126167481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_41 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (10332885755141 / 12500000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303130160581 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨41, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (10332885755141 / 12500000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303130160581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_42 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41314491985641 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460626835371 / 20000000000000 : ℝ))
      (E := (cell12308 ⟨42, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41314491985641 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (460626835371 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_43 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41297452826071 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303138157371 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨43, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41297452826071 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303138157371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_44 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (82560851053863 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151571080241 / 50000000000000 : ℝ))
      (E := (cell12308 ⟨44, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (82560851053863 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151571080241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_45 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (330107280587 / 400000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (230314612677 / 10000000000000 : ℝ))
      (E := (cell12308 ⟨45, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (330107280587 / 400000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (230314612677 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_46 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41246406450629 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151575086523 / 50000000000000 : ℝ))
      (E := (cell12308 ⟨46, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41246406450629 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151575086523 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_47 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (82458829287993 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303154121733 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨47, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (82458829287993 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303154121733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_48 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41212434638853 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (230315814813 / 10000000000000 : ℝ))
      (E := (cell12308 ⟨48, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41212434638853 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (230315814813 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_49 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (82390932841297 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151581066503 / 50000000000000 : ℝ))
      (E := (cell12308 ⟨49, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (82390932841297 / 100000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151581066503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_50 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (20589254987453 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303166133553 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨50, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (20589254987453 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303166133553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_51 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (20580782643611 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303170147879 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨51, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (20580782643611 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303170147879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_52 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (1285769760727 / 1562500000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (287896764361 / 12500000000000 : ℝ))
      (E := (cell12308 ⟨52, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (1285769760727 / 1562500000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (287896764361 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_53 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41127711128773 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (287897268777 / 12500000000000 : ℝ))
      (E := (cell12308 ⟨53, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41127711128773 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (287897268777 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_54 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41110801629561 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303182133329 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨54, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41110801629561 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303182133329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_55 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (4109390383151 / 5000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (92127444819 / 4000000000000 : ℝ))
      (E := (cell12308 ⟨55, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (4109390383151 / 5000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (92127444819 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_56 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (20538508860287 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303190108703 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨56, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (20538508860287 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303190108703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_57 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (16424057313111 / 20000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (8996851933 / 390625000000 : ℝ))
      (E := (cell12308 ⟨57, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (16424057313111 / 20000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (8996851933 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_58 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (20521640252107 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303198134673 / 100000000000000 : ℝ))
      (E := (cell12308 ⟨58, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (20521640252107 / 25000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (2303198134673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12308_59 : CellCertificate 12308 (224494178329823 / 2500000000000000 : ℝ) (853292519355609 / 500000000000000000 : ℝ) (172496337458789 / 5000000000000000 : ℝ)
    (cell12308 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · norm_num [cell12308]
  · have h := gap_lower (n := 12308) (a := (41026429371047 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151601053179 / 50000000000000 : ℝ))
      (E := (cell12308 ⟨59, by decide⟩).energy) (xi := (172496337458789 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12308 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12308]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12308])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12308) (a := (41026429371047 / 50000000000000 : ℝ)) (b := (8371074317 / 5000000000000 : ℝ)) (q := (1151601053179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12308])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12308]

theorem cert12309_40 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (20674302214713 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302983648863 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨40, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (20674302214713 / 25000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302983648863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_41 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (82663083325927 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460597522573 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨41, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (82663083325927 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460597522573 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_42 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41314490786633 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575747900189 / 25000000000000 : ℝ))
      (E := (cell12309 ⟨42, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41314490786633 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575747900189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_43 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (10324362946359 / 12500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302995612383 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨43, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (10324362946359 / 12500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2302995612383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_44 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (82560849288901 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575749897141 / 25000000000000 : ℝ))
      (E := (cell12309 ⟨44, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (82560849288901 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (575749897141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_45 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (82526818697659 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303003587459 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨45, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (82526818697659 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303003587459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_46 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41246405883801 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303007608253 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨46, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41246405883801 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303007608253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_47 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (16491765693867 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303011591043 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨47, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (16491765693867 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303011591043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_48 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (82424868773611 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460603118681 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨48, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (82424868773611 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460603118681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_49 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (82390932651331 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (18424156911 / 800000000000 : ℝ))
      (E := (cell12309 ⟨49, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (82390932651331 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (18424156911 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_50 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41178510036771 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303023591831 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨50, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41178510036771 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303023591831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_51 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (82323131011437 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303027584273 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨51, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (82323131011437 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303027584273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_52 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (1285769772443 / 1562500000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303031589097 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨52, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (1285769772443 / 1562500000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303031589097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_53 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (8225542331977 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303035603981 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨53, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (8225542331977 / 10000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303035603981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_54 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (16444320926663 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303039567357 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨54, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (16444320926663 / 20000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303039567357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_55 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (5136738084297 / 6250000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303043594533 / 100000000000000 : ℝ))
      (E := (cell12309 ⟨55, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (5136738084297 / 6250000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (2303043594533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_56 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (10269254679749 / 12500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287880945557 / 12500000000000 : ℝ))
      (E := (cell12309 ⟨56, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (10269254679749 / 12500000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287880945557 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_57 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (82120288873081 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (143940724507 / 6250000000000 : ℝ))
      (E := (cell12309 ⟨57, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (82120288873081 / 100000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (143940724507 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_58 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (2565205113319 / 3125000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460611111187 / 20000000000000 : ℝ))
      (E := (cell12309 ⟨58, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (2565205113319 / 3125000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (460611111187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12309_59 : CellCertificate 12309 (897947042472379 / 10000000000000000 : ℝ) (1706446346374873 / 1000000000000000000 : ℝ) (172481953225631 / 5000000000000000 : ℝ)
    (cell12309 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · norm_num [cell12309]
  · have h := gap_lower (n := 12309) (a := (41026430834851 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287882446323 / 12500000000000 : ℝ))
      (E := (cell12309 ⟨59, by decide⟩).energy) (xi := (172481953225631 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12309 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12309]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12309])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12309) (a := (41026430834851 / 50000000000000 : ℝ)) (b := (167407705041 / 100000000000000 : ℝ)) (q := (287882446323 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12309])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12309]

theorem cert12310_40 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82697205827007 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302841185379 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨40, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82697205827007 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302841185379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_41 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82663080611667 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151422589539 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨41, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82663080611667 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151422589539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_42 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82628979176151 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (92113965547 / 4000000000000 : ℝ))
      (E := (cell12310 ⟨42, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82628979176151 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (92113965547 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_43 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (2581090671577 / 3125000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (14392832017 / 625000000000 : ℝ))
      (E := (cell12310 ⟨43, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (2581090671577 / 3125000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (14392832017 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_44 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41280423762381 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575714282709 / 25000000000000 : ℝ))
      (E := (cell12310 ⟨44, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41280423762381 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (575714282709 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_45 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82526817249351 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302861162427 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨45, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82526817249351 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302861162427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_46 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82492810634689 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302865157827 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨46, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82492810634689 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302865157827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_47 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82458827651381 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (460573823187 / 20000000000000 : ℝ))
      (E := (cell12310 ⟨47, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82458827651381 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (460573823187 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_48 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82424868270181 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151436576611 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨48, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82424868270181 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151436576611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_49 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82390932461991 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151438575227 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨49, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82390932461991 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151438575227 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_50 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82357020197859 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302881105881 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨50, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82357020197859 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302881105881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_51 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82323131448977 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (143930320967 / 6250000000000 : ℝ))
      (E := (cell12310 ⟨51, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82323131448977 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (143930320967 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_52 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (16457853237337 / 20000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302889119207 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨52, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (16457853237337 / 20000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302889119207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_53 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82255424382463 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302893113711 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨53, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82255424382463 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302893113711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_54 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (41110803003969 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (46057942329 / 2000000000000 : ℝ))
      (E := (cell12310 ⟨54, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (41110803003969 / 50000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (46057942329 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_55 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82187811034877 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (57572528117 / 2500000000000 : ℝ))
      (E := (cell12310 ⟨55, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82187811034877 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (57572528117 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_56 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82154039435187 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302905135451 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨56, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82154039435187 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302905135451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_57 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (2053007279523 / 2500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151454543243 / 50000000000000 : ℝ))
      (E := (cell12310 ⟨57, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (2053007279523 / 2500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (1151454543243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_58 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (10260820780533 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302913092609 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨58, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (10260820780533 / 12500000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302913092609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12310_59 : CellCertificate 12310 (897917376268461 / 10000000000000000 : ℝ) (34126153531589 / 20000000000000000 : ℝ) (43116892862121 / 1250000000000000 : ℝ)
    (cell12310 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · norm_num [cell12310]
  · have h := gap_lower (n := 12310) (a := (82052864597547 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302917091153 / 100000000000000 : ℝ))
      (E := (cell12310 ⟨59, by decide⟩).energy) (xi := (43116892862121 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12310 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12310]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12310])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12310) (a := (82052864597547 / 100000000000000 : ℝ)) (b := (83696963019 / 50000000000000 : ℝ)) (q := (2302917091153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12310])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12310]

theorem cert12311_40 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82697202796143 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302698777027 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨40, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82697202796143 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302698777027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_41 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82663077898349 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575675685439 / 25000000000000 : ℝ))
      (E := (cell12311 ⟨41, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82663077898349 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575675685439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_42 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82628976779939 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (143919174413 / 6250000000000 : ℝ))
      (E := (cell12311 ⟨42, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82628976779939 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (143919174413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_43 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82594899410919 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302710747161 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨43, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82594899410919 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302710747161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_44 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41280422880723 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151357364249 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨44, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41280422880723 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151357364249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_45 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82526815801827 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302718734023 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨45, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82526815801827 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302718734023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_46 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (2062320237563 / 2500000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302722762919 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨46, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (2062320237563 / 2500000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302722762919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_47 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82458826834131 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151363377641 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨47, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82458826834131 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151363377641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_48 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82424867767417 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575682692171 / 25000000000000 : ℝ))
      (E := (cell12311 ⟨48, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82424867767417 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (575682692171 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_49 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82390932273277 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302734742743 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨49, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82390932273277 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302734742743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_50 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41178510161381 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302738734649 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨50, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41178510161381 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302738734649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_51 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (16464626377413 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302742742507 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨51, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (16464626377413 / 20000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302742742507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_52 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41144633468763 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302746705217 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨52, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41144633468763 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302746705217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_53 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41127712722813 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151375369209 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨53, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41127712722813 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151375369209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_54 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (5138850461437 / 6250000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (230275472157 / 10000000000000 : ℝ))
      (E := (cell12311 ⟨54, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (5138850461437 / 6250000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (230275472157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_55 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (5136738295087 / 6250000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302758710921 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨55, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (5136738295087 / 6250000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302758710921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_56 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (2567313794773 / 3125000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151381351757 / 50000000000000 : ℝ))
      (E := (cell12311 ⟨56, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (2567313794773 / 3125000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (1151381351757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_57 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (82120293489073 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302766696187 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨57, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (82120293489073 / 100000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302766696187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_58 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (41043284431297 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302770744697 / 100000000000000 : ℝ))
      (E := (cell12311 ⟨58, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (41043284431297 / 50000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (2302770744697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12311_59 : CellCertificate 12311 (897887714706397 / 10000000000000000 : ℝ) (426542257329863 / 250000000000000000 : ℝ) (344906384253277 / 10000000000000000 : ℝ)
    (cell12311 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · norm_num [cell12311]
  · have h := gap_lower (n := 12311) (a := (20513216881407 / 25000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (287846840903 / 12500000000000 : ℝ))
      (E := (cell12311 ⟨59, by decide⟩).energy) (xi := (344906384253277 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12311 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12311]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12311])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12311) (a := (20513216881407 / 25000000000000 : ℝ)) (b := (167380149331 / 100000000000000 : ℝ)) (q := (287846840903 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12311])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12311]

theorem cert12312_40 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82697199766261 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302556423809 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨40, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82697199766261 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302556423809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_41 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20665768796493 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (287820059637 / 12500000000000 : ℝ))
      (E := (cell12312 ⟨41, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20665768796493 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (287820059637 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_42 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20657243596157 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302564439051 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨42, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20657243596157 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302564439051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_43 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20648724333059 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302568426929 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨43, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20648724333059 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302568426929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_44 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (10320105499869 / 12500000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151286220177 / 50000000000000 : ℝ))
      (E := (cell12312 ⟨44, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (10320105499869 / 12500000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151286220177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_45 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (16505362871017 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302576419901 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨45, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (16505362871017 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302576419901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_46 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41246404185547 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302580423531 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨46, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41246404185547 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302580423531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_47 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41229413008793 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302584450211 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨47, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41229413008793 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302584450211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_48 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82424867265317 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151294219897 / 50000000000000 : ℝ))
      (E := (cell12312 ⟨48, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82424867265317 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151294219897 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_49 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82390932085189 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151296224831 / 50000000000000 : ℝ))
      (E := (cell12312 ⟨49, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82390932085189 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151296224831 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_50 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20589255112063 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302596419191 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨50, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20589255112063 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302596419191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_51 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (823231323257 / 1000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302600405381 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨51, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (823231323257 / 1000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302600405381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_52 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (41144633844437 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151302203061 / 50000000000000 : ℝ))
      (E := (cell12312 ⟨52, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (41144633844437 / 50000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (1151302203061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_53 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82255426509257 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302608419093 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨53, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82255426509257 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302608419093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_54 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (20555402189619 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302612441759 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨54, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (20555402189619 / 25000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302612441759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_55 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82187814408299 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460523282463 / 20000000000000 : ℝ))
      (E := (cell12312 ⟨55, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82187814408299 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460523282463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_56 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (82154043430637 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302620386819 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨56, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (82154043430637 / 100000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302620386819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_57 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (4106014789877 / 5000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460524884243 / 20000000000000 : ℝ))
      (E := (cell12312 ⟨57, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (4106014789877 / 5000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (460524884243 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_58 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (205216428703 / 250000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (143914274621 / 6250000000000 : ℝ))
      (E := (cell12312 ⟨58, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (205216428703 / 250000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (143914274621 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12312_59 : CellCertificate 12312 (448929028892523 / 5000000000000000 : ℝ) (426507601147347 / 250000000000000000 : ℝ) (34487763051877 / 1000000000000000 : ℝ)
    (cell12312 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · norm_num [cell12312]
  · have h := gap_lower (n := 12312) (a := (16410574090789 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302632419641 / 100000000000000 : ℝ))
      (E := (cell12312 ⟨59, by decide⟩).energy) (xi := (34487763051877 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12312 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12312]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12312])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12312) (a := (16410574090789 / 20000000000000 : ℝ)) (b := (167366374919 / 100000000000000 : ℝ)) (q := (2302632419641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12312])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12312]

theorem cert12313_40 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41348598368679 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575603546109 / 25000000000000 : ℝ))
      (E := (cell12313 ⟨40, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41348598368679 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575603546109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_41 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (10332884059317 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287802276113 / 12500000000000 : ℝ))
      (E := (cell12313 ⟨41, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (10332884059317 / 12500000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287802276113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_42 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (82628971990219 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302422201511 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨42, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (82628971990219 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302422201511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_43 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41297447627207 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (460485244161 / 20000000000000 : ℝ))
      (E := (cell12313 ⟨43, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41297447627207 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (460485244161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_44 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (516005263983 / 625000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302430207603 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨44, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (516005263983 / 625000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302430207603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_45 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41263406454563 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302434220061 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨45, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41263406454563 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302434220061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_46 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (20623201810103 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (143902387407 / 6250000000000 : ℝ))
      (E := (cell12313 ⟨46, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (20623201810103 / 25000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (143902387407 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_47 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (16491765040349 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (92097688029 / 4000000000000 : ℝ))
      (E := (cell12313 ⟨47, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (16491765040349 / 20000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (92097688029 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_48 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (82424866763881 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287805770819 / 12500000000000 : ℝ))
      (E := (cell12313 ⟨48, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (82424866763881 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (287805770819 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_49 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (3295637275909 / 4000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (18419601227 / 800000000000 : ℝ))
      (E := (cell12313 ⟨49, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (3295637275909 / 4000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (18419601227 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_50 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (82357020574327 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (230245415951 / 10000000000000 : ℝ))
      (E := (cell12313 ⟨50, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (82357020574327 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (230245415951 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_51 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41161566382441 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151229091531 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨51, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41161566382441 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151229091531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_52 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (82289268440731 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302462162929 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨52, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (82289268440731 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302462162929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_53 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (41127713786679 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302466155733 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨53, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (41127713786679 / 50000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302466155733 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_54 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (8222161013439 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302470158939 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨54, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (8222161013439 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302470158939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_55 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (82187816095597 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151237084901 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨55, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (82187816095597 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151237084901 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_56 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (8215404542889 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151239092683 / 50000000000000 : ℝ))
      (E := (cell12313 ⟨56, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (8215404542889 / 10000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (1151239092683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_57 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (1026503726329 / 1250000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575620535839 / 25000000000000 : ℝ))
      (E := (cell12313 ⟨57, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (1026503726329 / 1250000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (575620535839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_58 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (1026082176251 / 1250000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302486158591 / 100000000000000 : ℝ))
      (E := (cell12313 ⟨58, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (1026082176251 / 1250000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (2302486158591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12313_59 : CellCertificate 12313 (448914202751633 / 5000000000000000 : ℝ) (341178360476753 / 200000000000000000 : ℝ) (344848881692031 / 10000000000000000 : ℝ)
    (cell12313 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · norm_num [cell12313]
  · have h := gap_lower (n := 12313) (a := (82052873382499 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (460498033681 / 20000000000000 : ℝ))
      (E := (cell12313 ⟨59, by decide⟩).energy) (xi := (344848881692031 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12313 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12313]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12313])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12313) (a := (82052873382499 / 100000000000000 : ℝ)) (b := (83676301401 / 50000000000000 : ℝ)) (q := (460498033681 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12313])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12313]

theorem cert12314_40 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (20674298427359 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302272058907 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨40, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (20674298427359 / 25000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302272058907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_41 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (2066576744101 / 2500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460455210929 / 20000000000000 : ℝ))
      (E := (cell12314 ⟨41, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (2066576744101 / 2500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460455210929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_42 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (8262896959671 / 10000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302280019237 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨42, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (8262896959671 / 10000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302280019237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_43 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41297446588727 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (230228401123 / 10000000000000 : ℝ))
      (E := (cell12314 ⟨43, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41297446588727 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (230228401123 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_44 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (8256084047643 / 10000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575572007561 / 25000000000000 : ℝ))
      (E := (cell12314 ⟨44, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (8256084047643 / 10000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575572007561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_45 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (1650536229279 / 2000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302292016851 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨45, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (1650536229279 / 2000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302292016851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_46 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (10311600763809 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460459205803 / 20000000000000 : ℝ))
      (E := (cell12314 ⟨46, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (10311600763809 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460459205803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_47 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (82458824386607 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (287787500853 / 12500000000000 : ℝ))
      (E := (cell12314 ⟨47, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (82458824386607 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (287787500853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_48 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (8242486626311 / 10000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (143894000491 / 6250000000000 : ℝ))
      (E := (cell12314 ⟨48, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (8242486626311 / 10000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (143894000491 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_49 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (82390931710887 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302308030639 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨49, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (82390931710887 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302308030639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_50 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (82357020700989 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575578003637 / 25000000000000 : ℝ))
      (E := (cell12314 ⟨50, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (82357020700989 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575578003637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_51 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (82323133204611 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151158008291 / 50000000000000 : ℝ))
      (E := (cell12314 ⟨51, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (82323133204611 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151158008291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_52 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (10286158649137 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302319975639 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨52, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (10286158649137 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302319975639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_53 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (82255428637927 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460464801471 / 20000000000000 : ℝ))
      (E := (cell12314 ⟨53, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (82255428637927 / 100000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (460464801471 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_54 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41110805755367 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575581997797 / 25000000000000 : ℝ))
      (E := (cell12314 ⟨54, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41110805755367 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575581997797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_55 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41093908891643 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (287791497923 / 12500000000000 : ℝ))
      (E := (cell12314 ⟨55, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41093908891643 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (287791497923 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_56 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (16430809485499 / 20000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151167990493 / 50000000000000 : ℝ))
      (E := (cell12314 ⟨56, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (16430809485499 / 20000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151167990493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_57 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41060150207707 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151169990413 / 50000000000000 : ℝ))
      (E := (cell12314 ⟨57, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41060150207707 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (1151169990413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_58 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (41043288359617 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575585994883 / 25000000000000 : ℝ))
      (E := (cell12314 ⟨58, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (41043288359617 / 50000000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (575585994883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12314_59 : CellCertificate 12314 (448899378929959 / 5000000000000000 : ℝ) (213219152837137 / 125000000000000000 : ℝ) (172410068885821 / 5000000000000000 : ℝ)
    (cell12314 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · norm_num [cell12314]
  · have h := gap_lower (n := 12314) (a := (10256609538911 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302347973517 / 100000000000000 : ℝ))
      (E := (cell12314 ⟨59, by decide⟩).energy) (xi := (172410068885821 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12314 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12314]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12314])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12314) (a := (10256609538911 / 12500000000000 : ℝ)) (b := (8366941649 / 5000000000000 : ℝ)) (q := (2302347973517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12314])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12314]

theorem cert12315_40 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41348595341247 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143883120613 / 6250000000000 : ℝ))
      (E := (cell12315 ⟨40, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41348595341247 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143883120613 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_41 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16532613410897 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302133955589 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨41, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16532613410897 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302133955589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_42 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41314483602051 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151068975493 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨42, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41314483602051 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151068975493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_43 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41297445550677 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151070957883 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨43, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41297445550677 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151070957883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_44 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41280419358201 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (57553647707 / 2500000000000 : ℝ))
      (E := (cell12315 ⟨44, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41280419358201 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (57553647707 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_45 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16505362003911 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (287768740991 / 12500000000000 : ℝ))
      (E := (cell12315 ⟨45, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16505362003911 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (287768740991 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_46 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (3299712199251 / 4000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302153915041 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨46, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (3299712199251 / 4000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302153915041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_47 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20614705893043 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460431585477 / 20000000000000 : ℝ))
      (E := (cell12315 ⟨47, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20614705893043 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460431585477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_48 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (82424865763003 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (230216190481 / 10000000000000 : ℝ))
      (E := (cell12315 ⟨48, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (82424865763003 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (230216190481 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_49 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41195465762337 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151082952349 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨49, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41195465762337 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151082952349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_50 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20589255207059 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460433985073 / 20000000000000 : ℝ))
      (E := (cell12315 ⟨50, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20589255207059 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460433985073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_51 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (41161566822443 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151086952973 / 50000000000000 : ℝ))
      (E := (cell12315 ⟨51, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (41161566822443 / 50000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (1151086952973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_52 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (82289269945967 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143886118953 / 6250000000000 : ℝ))
      (E := (cell12315 ⟨52, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (82289269945967 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143886118953 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_53 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16451085940593 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302181914947 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨53, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16451085940593 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302181914947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_54 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (82221612887507 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143886617467 / 6250000000000 : ℝ))
      (E := (cell12315 ⟨54, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (82221612887507 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (143886617467 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_55 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (16437563894273 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (18417519297 / 800000000000 : ℝ))
      (E := (cell12315 ⟨55, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (16437563894273 / 20000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (18417519297 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_56 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (20538512356613 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302193891851 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨56, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (20538512356613 / 25000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302193891851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_57 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (4106015136241 / 5000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302197874521 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨57, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (4106015136241 / 5000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302197874521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_58 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (82086579338663 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302201915891 / 100000000000000 : ℝ))
      (E := (cell12315 ⟨58, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (82086579338663 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (2302201915891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12315_59 : CellCertificate 12315 (448884557426931 / 5000000000000000 : ℝ) (1705614665523891 / 1000000000000000000 : ℝ) (86197849689047 / 2500000000000000 : ℝ)
    (cell12315 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · norm_num [cell12315]
  · have h := gap_lower (n := 12315) (a := (82052879240313 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460441178827 / 20000000000000 : ℝ))
      (E := (cell12315 ⟨59, by decide⟩).energy) (xi := (86197849689047 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12315 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12315]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12315])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12315) (a := (82052879240313 / 100000000000000 : ℝ)) (b := (167325065451 / 100000000000000 : ℝ)) (q := (460441178827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12315])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12315]

theorem cert12316_40 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (20674296914133 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301987914557 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨40, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (20674296914133 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301987914557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_41 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82663064345869 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301991911737 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨41, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82663064345869 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301991911737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_42 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41314482406197 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301995938003 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨42, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41314482406197 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301995938003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_43 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (20648722256529 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301999934413 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨43, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (20648722256529 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2301999934413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_44 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (16512167391439 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (460400780103 / 20000000000000 : ℝ))
      (E := (cell12316 ⟨44, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (16512167391439 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (460400780103 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_45 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (41263404287971 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (460401578893 / 20000000000000 : ℝ))
      (E := (cell12316 ⟨45, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (41263404287971 / 50000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (460401578893 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_46 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82492803852821 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (28775148943 / 1250000000000 : ℝ))
      (E := (cell12316 ⟨46, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82492803852821 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (28775148943 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_47 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (2061470568961 / 2500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2302015903533 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨47, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (2061470568961 / 2500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2302015903533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_48 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (2060621631589 / 2500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1151009958157 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨48, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (2060621631589 / 2500000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1151009958157 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_49 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (16478186267817 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1151011946697 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨49, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (16478186267817 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1151011946697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_50 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82357020956069 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1151013945981 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨50, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82357020956069 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1151013945981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_51 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (20580783521427 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (57550797753 / 2500000000000 : ℝ))
      (E := (cell12316 ⟨51, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (20580783521427 / 25000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (57550797753 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_52 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82289270699347 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1151017943381 / 50000000000000 : ℝ))
      (E := (cell12316 ⟨52, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82289270699347 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (1151017943381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_53 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82255430768471 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (230203987851 / 10000000000000 : ℝ))
      (E := (cell12316 ⟨53, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82255430768471 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (230203987851 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_54 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82221614264709 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2302043882827 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨54, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82221614264709 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2302043882827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_55 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (16437564231967 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575511974241 / 25000000000000 : ℝ))
      (E := (cell12316 ⟨55, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (16437564231967 / 20000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575511974241 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_56 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82154051425761 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2302051858877 / 100000000000000 : ℝ))
      (E := (cell12316 ⟨56, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82154051425761 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (2302051858877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_57 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (4106015251727 / 5000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575513970887 / 25000000000000 : ℝ))
      (E := (cell12316 ⟨57, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (4106015251727 / 5000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575513970887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_58 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82086581958367 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575514962351 / 25000000000000 : ℝ))
      (E := (cell12316 ⟨58, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82086581958367 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (575514962351 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12316_59 : CellCertificate 12316 (448869738241979 / 5000000000000000 : ℝ) (341095226171733 / 200000000000000000 : ℝ) (86190666161063 / 2500000000000000 : ℝ)
    (cell12316 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · norm_num [cell12316]
  · have h := gap_lower (n := 12316) (a := (82052882169573 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (17984873993 / 781250000000 : ℝ))
      (E := (cell12316 ⟨59, by decide⟩).energy) (xi := (86190666161063 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12316 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12316]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12316])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12316) (a := (82052882169573 / 100000000000000 : ℝ)) (b := (33462260043 / 20000000000000 : ℝ)) (q := (17984873993 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12316])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12316]

theorem cert12317_40 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82697184631549 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301845954447 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨40, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82697184631549 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301845954447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_41 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41331530819097 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301849981821 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨41, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41331530819097 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301849981821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_42 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82628962421587 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (17983234221 / 781250000000 : ℝ))
      (E := (cell12317 ⟨42, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82628962421587 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (17983234221 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_43 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41297443475869 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150928974807 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨43, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41297443475869 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150928974807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_44 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (10320104399851 / 12500000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301861948149 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨44, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (10320104399851 / 12500000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301861948149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_45 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82526807133111 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (230186597529 / 10000000000000 : ℝ))
      (E := (cell12317 ⟨45, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82526807133111 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (230186597529 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_46 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82492802725109 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150934985683 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨46, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82492802725109 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150934985683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_47 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (20614705486353 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (230187393527 / 10000000000000 : ℝ))
      (E := (cell12317 ⟨47, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (20614705486353 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (230187393527 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_48 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (4121243238239 / 5000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (92075116983 / 4000000000000 : ℝ))
      (E := (cell12317 ⟨48, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (4121243238239 / 5000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (92075116983 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_49 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82390931154121 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301881937807 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨49, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82390931154121 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301881937807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_50 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (41178510542243 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460377194657 / 20000000000000 : ℝ))
      (E := (cell12317 ⟨50, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (41178510542243 / 50000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (460377194657 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_51 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (20580783631769 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301889970139 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨51, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (20580783631769 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301889970139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_52 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82289271453233 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150946963093 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨52, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82289271453233 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150946963093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_53 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (16451086366889 / 20000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (115094897853 / 5000000000000 : ℝ))
      (E := (cell12317 ⟨53, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (16451086366889 / 20000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (115094897853 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_54 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82221615642341 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150950971109 / 50000000000000 : ℝ))
      (E := (cell12317 ⟨54, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82221615642341 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (1150950971109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_55 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (16437564569739 / 20000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301905937901 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨55, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (16437564569739 / 20000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301905937901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_56 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82154053425421 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301909941151 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨56, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82154053425421 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301909941151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_57 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (20530076836143 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301913948801 / 100000000000000 : ℝ))
      (E := (cell12317 ⟨57, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (20530076836143 / 25000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (2301913948801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_58 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (10260823072293 / 12500000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (71934936171 / 3125000000000 : ℝ))
      (E := (cell12317 ⟨58, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (10260823072293 / 12500000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (71934936171 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12317_59 : CellCertificate 12317 (224427460687267 / 2500000000000000 : ℝ) (341067523739187 / 200000000000000000 : ℝ) (344733935434421 / 10000000000000000 : ℝ)
    (cell12317 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · norm_num [cell12317]
  · have h := gap_lower (n := 12317) (a := (82052885099069 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (287740238053 / 12500000000000 : ℝ))
      (E := (cell12317 ⟨59, by decide⟩).energy) (xi := (344733935434421 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12317 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12317]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12317])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12317) (a := (82052885099069 / 100000000000000 : ℝ)) (b := (167297537271 / 100000000000000 : ℝ)) (q := (287740238053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12317])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12317]

theorem cert12318_40 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (16539436321509 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575426027047 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨40, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (16539436321509 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575426027047 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_41 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41331529465729 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301708107113 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨41, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41331529465729 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301708107113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_42 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82628960031679 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150856038923 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨42, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82628960031679 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150856038923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_43 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (4129744243911 / 5000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301716078931 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨43, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (4129744243911 / 5000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301716078931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_44 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82560833441243 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (460344021997 / 20000000000000 : ℝ))
      (E := (cell12318 ⟨44, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82560833441243 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (460344021997 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_45 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82526805691061 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301724111579 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨45, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82526805691061 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301724111579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_46 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41246400799069 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (115086404141 / 5000000000000 : ℝ))
      (E := (cell12318 ⟨46, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41246400799069 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (115086404141 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_47 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41229410566543 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301732081473 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨47, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41229410566543 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301732081473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_48 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (10303108033333 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301736047387 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨48, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (10303108033333 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301736047387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_49 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (4119546548489 / 5000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301740096861 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨49, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (4119546548489 / 5000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301740096861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_50 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82357021213489 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150872025723 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨50, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82357021213489 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150872025723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_51 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (8232313496899 / 10000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575437021501 / 25000000000000 : ℝ))
      (E := (cell12318 ⟨51, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (8232313496899 / 10000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (575437021501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_52 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41144636103813 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301752080511 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨52, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41144636103813 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301752080511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_53 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82255432900887 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301756091583 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨53, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82255432900887 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301756091583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_54 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41110808510201 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (460352011529 / 20000000000000 : ℝ))
      (E := (cell12318 ⟨54, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41110808510201 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (460352011529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_55 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (41093912268973 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150882017469 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨55, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (41093912268973 / 50000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150882017469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_56 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (10269256928179 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (230176807959 / 10000000000000 : ℝ))
      (E := (cell12318 ⟨56, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (10269256928179 / 12500000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (230176807959 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_57 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (82120309654917 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150886035141 / 50000000000000 : ℝ))
      (E := (cell12318 ⟨57, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (82120309654917 / 100000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (1150886035141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_58 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (16417317439719 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301776062699 / 100000000000000 : ℝ))
      (E := (cell12318 ⟨58, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (16417317439719 / 20000000000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (2301776062699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12318_59 : CellCertificate 12318 (224420053412013 / 2500000000000000 : ℝ) (852599564515109 / 500000000000000000 : ℝ) (2154407569533 / 62500000000000 : ℝ)
    (cell12318 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · norm_num [cell12318]
  · have h := gap_lower (n := 12318) (a := (25641527509 / 31250000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (460356010651 / 20000000000000 : ℝ))
      (E := (cell12318 ⟨59, by decide⟩).energy) (xi := (2154407569533 / 62500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12318 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12318]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12318])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12318) (a := (25641527509 / 31250000000 : ℝ)) (b := (83641888309 / 50000000000000 : ℝ)) (q := (460356010651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12318])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12318]

theorem cert12319_40 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (2067429464613 / 2500000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (143847644817 / 6250000000000 : ℝ))
      (E := (cell12319 ⟨40, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (2067429464613 / 2500000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (143847644817 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_41 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (4133152811283 / 5000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301566287613 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨41, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (4133152811283 / 5000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301566287613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_42 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82628957642671 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (230157028943 / 10000000000000 : ℝ))
      (E := (cell12319 ⟨42, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82628957642671 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (230157028943 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_43 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41297441402781 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150787131791 / 50000000000000 : ℝ))
      (E := (cell12319 ⟨43, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41297441402781 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150787131791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_44 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41280415842249 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301578268417 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨44, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41280415842249 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301578268417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_45 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82526804249793 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (230158230333 / 10000000000000 : ℝ))
      (E := (cell12319 ⟨45, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82526804249793 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (230158230333 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_46 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (8249280047191 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (11507931249 / 500000000000 : ℝ))
      (E := (cell12319 ⟨46, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (8249280047191 / 10000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (11507931249 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_47 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41229410160731 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301590283267 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨47, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41229410160731 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301590283267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_48 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82424863769211 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301594284751 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨48, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82424863769211 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301594284751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_49 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (5149433174129 / 6250000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301598252711 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨49, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (5149433174129 / 6250000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301598252711 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_50 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82357021343077 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301602244333 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨50, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82357021343077 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301602244333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_51 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82323135411449 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575401564429 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨51, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82323135411449 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575401564429 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_52 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41144636481263 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460322058149 / 20000000000000 : ℝ))
      (E := (cell12319 ⟨52, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41144636481263 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (460322058149 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_53 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (20563858491949 / 25000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (14385089263 / 625000000000 : ℝ))
      (E := (cell12319 ⟨53, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (20563858491949 / 25000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (14385089263 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_54 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82221618398891 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301618288149 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨54, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82221618398891 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301618288149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_55 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41093913113793 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150811123569 / 50000000000000 : ℝ))
      (E := (cell12319 ⟨55, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41093913113793 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (1150811123569 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_56 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (16430811485159 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301626274191 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨56, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (16430811485159 / 20000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301626274191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_57 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (41060155982787 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301630247989 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨57, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (41060155982787 / 50000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301630247989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_58 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (1026082372739 / 1250000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575408570837 / 25000000000000 : ℝ))
      (E := (cell12319 ⟨58, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (1026082372739 / 1250000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (575408570837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12319_59 : CellCertificate 12319 (224412647294943 / 2500000000000000 : ℝ) (1705060661856033 / 1000000000000000000 : ℝ) (43084561464427 / 1250000000000000 : ℝ)
    (cell12319 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · norm_num [cell12319]
  · have h := gap_lower (n := 12319) (a := (82052890958767 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301638258439 / 100000000000000 : ℝ))
      (E := (cell12319 ⟨59, by decide⟩).energy) (xi := (43084561464427 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12319 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12319]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12319])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12319) (a := (82052890958767 / 100000000000000 : ℝ)) (b := (167270018257 / 100000000000000 : ℝ)) (q := (2301638258439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12319])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12319]

theorem cert12320_40 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82697175562473 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301420581101 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨40, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82697175562473 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301420581101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_41 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (41331526760401 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575356145513 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨41, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (41331526760401 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575356145513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_42 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82628955254561 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (4494977649 / 195312500000 : ℝ))
      (E := (cell12320 ⟨42, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82628955254561 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (4494977649 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_43 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (20648720183441 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (46028651247 / 2000000000000 : ℝ))
      (E := (cell12320 ⟨43, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (20648720183441 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (46028651247 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_44 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82560829928573 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301436541053 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨44, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82560829928573 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301436541053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_45 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (16505360561861 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150720275273 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨45, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (16505360561861 / 20000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150720275273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_46 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (41246399673211 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (57536113279 / 2500000000000 : ℝ))
      (E := (cell12320 ⟨46, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (41246399673211 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (57536113279 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_47 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (4122940975527 / 5000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150724270327 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨47, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (4122940975527 / 5000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150724270327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_48 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (4121243163621 / 5000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575363129719 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨48, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (4121243163621 / 5000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575363129719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_49 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82390930602971 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575364130801 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨49, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82390930602971 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575364130801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_50 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82357021473249 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301460551949 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨50, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82357021473249 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301460551949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_51 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (41161567927227 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301464544243 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨51, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (41161567927227 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301464544243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_52 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (20572318429483 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575367139223 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨52, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (20572318429483 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575367139223 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_53 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (82255435035173 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (287684066069 / 12500000000000 : ℝ))
      (E := (cell12320 ⟨53, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (82255435035173 / 100000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (287684066069 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_54 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (8222161977781 / 10000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301476515651 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨54, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (8222161977781 / 10000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301476515651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_55 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (5136739244851 / 6250000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (28768506443 / 1250000000000 : ℝ))
      (E := (cell12320 ⟨55, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (5136739244851 / 6250000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (28768506443 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_56 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (20538514856627 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301484524959 / 100000000000000 : ℝ))
      (E := (cell12320 ⟨56, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (20538514856627 / 25000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (2301484524959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_57 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (1283129910571 / 1562500000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150744270517 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨57, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (1283129910571 / 1562500000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150744270517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_58 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (41043296219959 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575373125289 / 25000000000000 : ℝ))
      (E := (cell12320 ⟨58, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (41043296219959 / 50000000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (575373125289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12320_59 : CellCertificate 12320 (89762096934309 / 1000000000000000 : ℝ) (852461108583951 / 500000000000000000 : ℝ) (344647777203417 / 10000000000000000 : ℝ)
    (cell12320 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · norm_num [cell12320]
  · have h := gap_lower (n := 12320) (a := (10256611736121 / 12500000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150748259989 / 50000000000000 : ℝ))
      (E := (cell12320 ⟨59, by decide⟩).energy) (xi := (344647777203417 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12320 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12320]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12320])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12320) (a := (10256611736121 / 12500000000000 : ℝ)) (b := (167256262187 / 100000000000000 : ℝ)) (q := (1150748259989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12320])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12320]

theorem cert12321_40 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (16539434508281 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575319725069 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨40, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (16539434508281 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575319725069 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_41 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41331525408441 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301282931703 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨41, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41331525408441 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301282931703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_42 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (82628952867351 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (115064343921 / 5000000000000 : ℝ))
      (E := (cell12321 ⟨42, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (82628952867351 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (115064343921 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_43 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (3303795146513 / 4000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150645458229 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨43, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (3303795146513 / 4000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150645458229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_44 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (82560828173469 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (460258985579 / 20000000000000 : ℝ))
      (E := (cell12321 ⟨44, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (82560828173469 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (460258985579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_45 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (82526801369597 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150649456029 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨45, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (82526801369597 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150649456029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_46 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20623199555419 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (46026057361 / 2000000000000 : ℝ))
      (E := (cell12321 ⟨46, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20623199555419 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (46026057361 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_47 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (82458818700321 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301306912509 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨47, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (82458818700321 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301306912509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_48 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (82424862776293 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575327716889 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨48, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (82424862776293 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575327716889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_49 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41195465210251 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301314908339 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨49, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41195465210251 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301314908339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_50 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41178510802003 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301318856407 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨50, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41178510802003 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301318856407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_51 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20580784074501 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301322886621 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨51, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20580784074501 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301322886621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_52 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (16457854894769 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301326878951 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨52, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (16457854894769 / 20000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301326878951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_53 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (41127718051509 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (460266178003 / 20000000000000 : ℝ))
      (E := (cell12321 ⟨53, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (41127718051509 / 50000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (460266178003 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_54 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20555405289289 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150667429117 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨54, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20555405289289 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150667429117 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_55 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20546957402009 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575334724727 / 25000000000000 : ℝ))
      (E := (cell12321 ⟨55, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20546957402009 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (575334724727 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_56 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (82154061427573 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150671445489 / 50000000000000 : ℝ))
      (E := (cell12321 ⟨56, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (82154061427573 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (1150671445489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_57 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (3284812663513 / 4000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230134689031 / 10000000000000 : ℝ))
      (E := (cell12321 ⟨57, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (3284812663513 / 4000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (230134689031 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_58 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (82086595060991 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301350893523 / 100000000000000 : ℝ))
      (E := (cell12321 ⟨58, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (82086595060991 / 100000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (2301350893523 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12321_59 : CellCertificate 12321 (897591354136869 / 10000000000000000 : ℝ) (1704783794960347 / 1000000000000000000 : ℝ) (10769345862121 / 312500000000000 : ℝ)
    (cell12321 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · norm_num [cell12321]
  · have h := gap_lower (n := 12321) (a := (20513224204851 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (287669362129 / 12500000000000 : ℝ))
      (E := (cell12321 ⟨59, by decide⟩).energy) (xi := (10769345862121 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12321 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12321]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12321])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12321) (a := (20513224204851 / 25000000000000 : ℝ)) (b := (83621254203 / 50000000000000 : ℝ)) (q := (287669362129 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12321])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12321]

theorem cert12322_40 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41348584760657 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575284333327 / 25000000000000 : ℝ))
      (E := (cell12322 ⟨40, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41348584760657 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575284333327 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_41 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82663048113901 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575285334141 / 25000000000000 : ℝ))
      (E := (cell12322 ⟨41, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82663048113901 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575285334141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_42 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (1032861881013 / 1250000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301145314583 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨42, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (1032861881013 / 1250000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301145314583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_43 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41297438296373 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301149325903 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨43, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41297438296373 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301149325903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_44 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82560826419183 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150576655669 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨44, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82560826419183 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150576655669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_45 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (8252679993067 / 10000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460231465807 / 20000000000000 : ℝ))
      (E := (cell12322 ⟨45, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (8252679993067 / 10000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460231465807 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_46 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82492797097671 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301161319323 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨46, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82492797097671 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301161319323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_47 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82458817890803 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150582640543 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨47, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82458817890803 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150582640543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_48 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (20606215570207 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (287646166349 / 12500000000000 : ℝ))
      (E := (cell12322 ⟨48, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (20606215570207 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (287646166349 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_49 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (1287358284979 / 1562500000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301173290277 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨49, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (1287358284979 / 1562500000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301173290277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_50 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (41178510867673 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575294318899 / 25000000000000 : ℝ))
      (E := (cell12322 ⟨50, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (41178510867673 / 50000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575294318899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_51 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (823231367421 / 1000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301181284847 / 100000000000000 : ℝ))
      (E := (cell12322 ⟨51, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (823231367421 / 1000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (2301181284847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_52 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (10286159403783 / 12500000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575296328979 / 25000000000000 : ℝ))
      (E := (cell12322 ⟨52, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (10286159403783 / 12500000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575296328979 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_53 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (8225543717133 / 10000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460237861491 / 20000000000000 : ℝ))
      (E := (cell12322 ⟨53, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (8225543717133 / 10000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460237861491 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_54 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82221622536931 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460238663179 / 20000000000000 : ℝ))
      (E := (cell12322 ⟨54, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82221622536931 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460238663179 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_55 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (16437566259769 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150598639709 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨55, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (16437566259769 / 20000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150598639709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_56 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (20538515857247 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150600656583 / 50000000000000 : ℝ))
      (E := (cell12322 ⟨56, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (20538515857247 / 25000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (1150600656583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_57 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (82120318899419 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (287650661977 / 12500000000000 : ℝ))
      (E := (cell12322 ⟨57, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (82120318899419 / 100000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (287650661977 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_58 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (2565206177573 / 3125000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575302320763 / 25000000000000 : ℝ))
      (E := (cell12322 ⟨58, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (2565206177573 / 3125000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (575302320763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12322_59 : CellCertificate 12322 (224390435889993 / 2500000000000000 : ℝ) (340929079045579 / 200000000000000000 : ℝ) (43073795358421 / 1250000000000000 : ℝ)
    (cell12322 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · norm_num [cell12322]
  · have h := gap_lower (n := 12322) (a := (3282115990003 / 4000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460242654257 / 20000000000000 : ℝ))
      (E := (cell12322 ⟨59, by decide⟩).energy) (xi := (43073795358421 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12322 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12322]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12322])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12322) (a := (3282115990003 / 4000000000000 : ℝ)) (b := (33445751383 / 20000000000000 : ℝ)) (q := (460242654257 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12322])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12322]

theorem cert12323_40 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82697166502201 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (143812238843 / 6250000000000 : ℝ))
      (E := (cell12323 ⟨40, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82697166502201 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (143812238843 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_41 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82663045411857 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (14381248729 / 625000000000 : ℝ))
      (E := (cell12323 ⟨41, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82663045411857 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (14381248729 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_42 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82628948095627 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (287625475753 / 12500000000000 : ℝ))
      (E := (cell12323 ⟨42, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82628948095627 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (287625475753 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_43 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (3303794980941 / 4000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575251947673 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨43, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (3303794980941 / 4000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575251947673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_44 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41280412332859 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301011808989 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨44, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41280412332859 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301011808989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_45 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82526798492523 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301015801483 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨45, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82526798492523 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301015801483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_46 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82492795974407 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (143813739133 / 6250000000000 : ℝ))
      (E := (cell12323 ⟨46, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82492795974407 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (143813739133 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_47 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41229408540993 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (71906994469 / 3125000000000 : ℝ))
      (E := (cell12323 ⟨47, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41229408540993 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (71906994469 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_48 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (3296994471441 / 4000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301027790793 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨48, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (3296994471441 / 4000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301027790793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_49 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41195465028717 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301031786859 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨49, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41195465028717 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301031786859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_50 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82357021867271 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150517904759 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨50, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82357021867271 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150517904759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_51 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (4116156859337 / 5000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (460207959579 / 20000000000000 : ℝ))
      (E := (cell12323 ⟨51, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (4116156859337 / 5000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (460207959579 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_52 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20572318996797 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301043808797 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨52, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20572318996797 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301043808797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_53 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (20563859560027 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575261945219 / 25000000000000 : ℝ))
      (E := (cell12323 ⟨53, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (20563859560027 / 25000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (575261945219 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_54 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41110811958567 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301051770561 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨54, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41110811958567 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301051770561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_55 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82187832990043 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301055775097 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨55, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82187832990043 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301055775097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_56 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41077032715377 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150529895761 / 50000000000000 : ℝ))
      (E := (cell12323 ⟨56, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41077032715377 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (1150529895761 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_57 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (3284812848453 / 4000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (460212751511 / 20000000000000 : ℝ))
      (E := (cell12323 ⟨57, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (3284812848453 / 4000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (460212751511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_58 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (41043300151977 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (230106778801 / 10000000000000 : ℝ))
      (E := (cell12323 ⟨58, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (41043300151977 / 50000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (230106778801 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12323_59 : CellCertificate 12323 (44876606880563 / 500000000000000 : ℝ) (1704507017965071 / 1000000000000000000 : ℝ) (21535103940031 / 625000000000000 : ℝ)
    (cell12323 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · norm_num [cell12323]
  · have h := gap_lower (n := 12323) (a := (82052902680981 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301071761053 / 100000000000000 : ℝ))
      (E := (cell12323 ⟨59, by decide⟩).energy) (xi := (21535103940031 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12323 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12323]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12323])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12323) (a := (82052902680981 / 100000000000000 : ℝ)) (b := (5225468991 / 3125000000000 : ℝ)) (q := (2301071761053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12323])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12323]

theorem cert12324_40 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41348581742033 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150427182409 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨40, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41348581742033 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150427182409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_41 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82663042710751 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150429185331 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨41, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82663042710751 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150429185331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_42 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (10328618213889 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300862352743 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨42, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (10328618213889 / 12500000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300862352743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_43 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82594872455163 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150433184801 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨43, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82594872455163 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150433184801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_44 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82560822913071 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (35951099407 / 1562500000000 : ℝ))
      (E := (cell12324 ⟨44, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82560822913071 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (35951099407 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_45 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (16505359411031 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300874388229 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨45, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (16505359411031 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300874388229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_46 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82492794851883 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300878388469 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨46, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82492794851883 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300878388469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_47 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82458816273871 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150441180827 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨47, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82458816273871 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150441180827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_48 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82424861291883 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150443182677 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨48, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82424861291883 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150443182677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_49 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41195464938417 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (71902823099 / 3125000000000 : ℝ))
      (E := (cell12324 ⟨49, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41195464938417 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (71902823099 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_50 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82357021999779 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460178868057 / 20000000000000 : ℝ))
      (E := (cell12324 ⟨50, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82357021999779 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (460178868057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_51 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (3292925505277 / 4000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575224591699 / 25000000000000 : ℝ))
      (E := (cell12324 ⟨51, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (3292925505277 / 4000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (575224591699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_52 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82289276744619 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150451178797 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨52, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82289276744619 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150451178797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_53 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41127719654677 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300906369291 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨53, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41127719654677 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300906369291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_54 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (16444325059553 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300910340309 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨54, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (16444325059553 / 20000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300910340309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_55 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82187834681631 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150457163441 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨55, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82187834681631 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150457163441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_56 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (8215406743287 / 10000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (46018366521 / 2000000000000 : ℝ))
      (E := (cell12324 ⟨56, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (8215406743287 / 10000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (46018366521 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_57 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41060161761771 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150461167319 / 50000000000000 : ℝ))
      (E := (cell12324 ⟨57, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41060161761771 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (1150461167319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_58 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (41043301462923 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (143807896829 / 6250000000000 : ℝ))
      (E := (cell12324 ⟨58, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (41043301462923 / 50000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (143807896829 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

theorem cert12324_59 : CellCertificate 12324 (897502536289599 / 10000000000000000 : ℝ) (1704368663166403 / 1000000000000000000 : ℝ) (172266484052923 / 5000000000000000 : ℝ)
    (cell12324 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · norm_num [cell12324]
  · have h := gap_lower (n := 12324) (a := (82052905612121 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300930366339 / 100000000000000 : ℝ))
      (E := (cell12324 ⟨59, by decide⟩).energy) (xi := (172266484052923 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12324 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12324]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12324])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12324) (a := (82052905612121 / 100000000000000 : ℝ)) (b := (167201260797 / 100000000000000 : ℝ)) (q := (2300930366339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12324])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12324]

end BstLean.Part263
